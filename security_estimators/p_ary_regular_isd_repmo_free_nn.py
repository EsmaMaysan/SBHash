import argparse
import csv
import math
import sys
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from pathlib import Path

import numpy as np

TAU_OFFSETS = (-8, -6, -4, -2, -1, 0, 1, 2, 4, 6, 8)


def logadd2(a, b):
    a, b = np.broadcast_arrays(np.asarray(a, dtype=float), np.asarray(b, dtype=float))
    maximum = np.maximum(a, b)
    result = np.full(maximum.shape, -np.inf)
    finite = np.isfinite(maximum)
    result[finite] = maximum[finite] + np.log2(
        np.exp2(a[finite] - maximum[finite])
        + np.exp2(b[finite] - maximum[finite])
    )
    return result


def poisson_nonzero_log2(log2_mean):
    values = np.asarray(log2_mean, dtype=float)
    result = np.empty_like(values)
    small = values < -40.0
    large = values > 6.0
    middle = ~(small | large)
    result[small] = values[small]
    result[large] = 0.0
    result[middle] = np.log2(-np.expm1(-np.exp2(values[middle])))
    return result


def balanced_values(total, count, lower, upper):
    if count == 0:
        return () if total == 0 else None
    if total < count * lower or total > count * upper:
        return None
    quotient, remainder = divmod(total - count * lower, count)
    return (
        (lower + quotient + 1,) * remainder
        + (lower + quotient,) * (count - remainder)
    )


def make_profile(ell, r, m, lam, u, r_u):
    if not (0 <= lam < r and 0 <= u <= m):
        return None
    active = balanced_values(r_u, u, 0, ell - 1)
    inactive = balanced_values(r - lam - r_u, m - u, 1, ell)
    if active is None or inactive is None:
        return None
    blocks = []
    for index in range(max(len(active), len(inactive))):
        if index < len(active):
            blocks.append((True, active[index]))
        if index < len(inactive):
            blocks.append((False, inactive[index]))
    return tuple(blocks[::2]), tuple(blocks[1::2])


@lru_cache(maxsize=2048)
def half_tables(p, ell, half):
    size = len(half)
    capacity = np.full(size + 1, -np.inf)
    capacity[0] = 0.0
    representations = np.full((size + 1, size + 1), -np.inf)
    representations[0, 0] = 0.0
    for degree, (active, pivots) in enumerate(half):
        choices = (ell - pivots) * (p - 1)
        next_capacity = np.full_like(capacity, -np.inf)
        next_capacity[:degree + 1] = capacity[:degree + 1]
        if choices > 0:
            next_capacity[1:degree + 2] = logadd2(
                next_capacity[1:degree + 2],
                capacity[:degree + 1] + math.log2(choices),
            )
        capacity = next_capacity
        previous = representations[:degree + 1, :degree + 1]
        following = np.full_like(representations, -np.inf)
        if active:
            following[1:degree + 2, :degree + 1] = logadd2(
                following[1:degree + 2, :degree + 1], previous
            )
            following[:degree + 1, 1:degree + 2] = logadd2(
                following[:degree + 1, 1:degree + 2], previous
            )
            following[1:degree + 2, 1:degree + 2] = logadd2(
                following[1:degree + 2, 1:degree + 2],
                previous + math.log2(p - 2),
            )
        else:
            following[:degree + 1, :degree + 1] = previous
            if choices > 0:
                following[1:degree + 2, 1:degree + 2] = logadd2(
                    following[1:degree + 2, 1:degree + 2],
                    previous + math.log2(choices),
                )
        representations = following
    return capacity, representations.diagonal().copy()


def rank_log2_probability(p, r, lam):
    return sum(math.log2(1.0 - p ** (-j)) for j in range(lam + 1, r + 1))


def profile_log2_mean(p, ell, r, half1, half2):
    total = 0.0
    for active, pivots in half1 + half2:
        choices = ((ell - pivots) if active else pivots) * (p - 1)
        if choices <= 0:
            return -math.inf
        total += math.log2(choices)
    return total - r * math.log2(p)


def estimate_profile(p, ell, r, m, lam, u, r_u, tau_offsets=TAU_OFFSETS, all_tau=False):
    profile = make_profile(ell, r, m, lam, u, r_u)
    if profile is None:
        return None
    half1, half2 = profile
    c1, r1 = half_tables(p, ell, half1)
    c2, r2 = half_tables(p, ell, half2)
    indices1 = np.flatnonzero(np.isfinite(c1) & np.isfinite(r1))
    indices2 = np.flatnonzero(np.isfinite(c2) & np.isfinite(r2))
    if not len(indices1) or not len(indices2):
        return None
    leaf1 = c1[indices1, None]
    leaf2 = c2[None, indices2]
    log_representations = r1[indices1, None] + r2[None, indices2]
    log_mean = profile_log2_mean(p, ell, r, half1, half2)
    if not math.isfinite(log_mean):
        return None
    log_p = math.log2(p)
    tau_centers = np.rint(log_representations / log_p)
    log_rank = rank_log2_probability(p, r, lam)
    base_cost = logadd2(3.0 * math.log2(r), np.maximum(leaf1, leaf2) + 2.0)
    best = None
    best_key = None
    for tau in range(lam + 1):
        permitted = np.ones_like(log_representations, dtype=bool)
        if not all_tau and tau not in (0, lam):
            permitted = np.zeros_like(log_representations, dtype=bool)
            for offset in tau_offsets:
                permitted |= tau_centers + offset == tau
            if not np.any(permitted):
                continue
        intermediate = leaf1 + leaf2 - tau * log_p
        survival = poisson_nonzero_log2(log_representations - tau * log_p)
        success = poisson_nonzero_log2(log_mean + survival)
        iteration = logadd2(base_cost, intermediate + 1.0)
        work = iteration - log_rank - success
        work = np.where((intermediate >= -20.0) & permitted, work, np.inf)
        minimum = float(np.min(work))
        if not math.isfinite(minimum):
            continue
        if best_key is not None and minimum > best_key[0]:
            continue
        locations = np.argwhere(work == minimum)
        for i, j in locations:
            a1 = int(indices1[i])
            a2 = int(indices2[j])
            memory = max(float(leaf1[i, 0]), float(leaf2[0, j]), float(intermediate[i, j]))
            key = (minimum, memory, tau, a1, a2)
            if best_key is not None and key >= best_key:
                continue
            best_key = key
            details = (
                a1, a2, tau, float(leaf1[i, 0]), float(leaf2[0, j]),
                float(log_representations[i, j]), float(log_mean),
                float(survival[i, j]), float(success[i, j]), float(iteration[i, j]),
            )
            best = {
                'free_nn_work': minimum,
                'lam': lam,
                'u': u,
                'R_U': r_u,
                'details': details,
            }
    return best


def profile_grid(scan, p, ell, r, m):
    if (p, ell, r, m) != (5, 64, 528, 192):
        raise ValueError('The archived stageA/refine grids use p=5, ell=64, r=528, m=192.')
    profiles = set()
    if scan == 'refine':
        pairs = ((lam, u) for lam in range(140, 191, 5) for u in range(136, 170, 3))
    else:
        lambdas = sorted(set(range(1, r, 32)) | {r - 1})
        active_counts = sorted(set(range(2, m + 1, 16)) | {m})
        pairs = ((lam, u) for lam in lambdas for u in active_counts)
        profiles.update({(208, 120, 0), (225, 108, 0), (349, 132, 0)})
    for lam, u in pairs:
        pivots = r - lam
        lower = max(0, pivots - (m - u) * ell)
        upper = min(u * (ell - 1), pivots - (m - u))
        if lower > upper:
            continue
        allocations = {lower, upper, round(pivots * u / m)}
        if scan == 'refine':
            allocations.update(range(120, 221, 10))
        else:
            allocations.add((lower + upper) // 2)
        for r_u in allocations:
            if lower <= r_u <= upper:
                profiles.add((lam, u, r_u))
    return sorted(profiles)


def estimate_task(task):
    return estimate_profile(*task)


def run_scan(scan, p, ell, r, m, workers=1, tau_offsets=TAU_OFFSETS, all_tau=False):
    profiles = profile_grid(scan, p, ell, r, m)
    tasks = [(p, ell, r, m, *profile, tau_offsets, all_tau) for profile in profiles]
    rows = []
    executor = ProcessPoolExecutor(max_workers=workers) if workers > 1 else None
    try:
        iterator = executor.map(estimate_task, tasks) if executor else map(estimate_task, tasks)
        for index, row in enumerate(iterator, 1):
            if row is not None:
                rows.append(row)
            if index % 100 == 0 or index == len(tasks):
                print(f'{scan}: {index}/{len(tasks)} profiles', file=sys.stderr, flush=True)
    finally:
        if executor:
            executor.shutdown()
    rows.sort(key=lambda row: (row['free_nn_work'], row['lam'], row['u'], row['R_U']))
    return rows


def main():
    parser = argparse.ArgumentParser(
        description='Rep-MO free-NN benchmark: final matching and candidate-verification costs are set to zero; regular-completion feasibility enters the success model. The program does not read existing CSV results.'
    )
    parser.add_argument('--p', type=int, default=5)
    parser.add_argument('--ell', type=int, default=64)
    parser.add_argument('--r', type=int, default=528)
    parser.add_argument('--m', type=int, default=192)
    parser.add_argument('--lam', type=int, default=185)
    parser.add_argument('--u', type=int, default=157)
    parser.add_argument('--r-u', type=int, default=220)
    parser.add_argument('--scan', choices=['profile', 'stageA', 'refine'], default='profile')
    parser.add_argument('--workers', type=int, default=1)
    parser.add_argument('--all-tau', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.p < 3 or any(args.p % divisor == 0 for divisor in range(2, math.isqrt(args.p) + 1)):
        parser.error('p must be an odd prime.')
    if args.ell < 2 or args.r < 1 or args.m < 1 or args.workers < 1:
        parser.error('ell >= 2, r >= 1, m >= 1 and workers >= 1 are required.')
    if args.output and args.output.exists():
        parser.error('The output already exists; choose a new filename to preserve existing CSVs.')
    if args.scan == 'profile':
        result = estimate_profile(args.p, args.ell, args.r, args.m, args.lam, args.u, args.r_u, TAU_OFFSETS, args.all_tau)
        if result is None:
            parser.error('The requested profile is infeasible.')
        rows = [result]
    else:
        rows = run_scan(args.scan, args.p, args.ell, args.r, args.m, args.workers, TAU_OFFSETS, args.all_tau)
    if not rows:
        parser.error('No feasible profile was found.')
    best = rows[0]
    a1, a2, tau = best['details'][:3]
    print('Rep-MO free-NN benchmark')
    print(f'p={args.p}, ell={args.ell}, r={args.r}, m={args.m}')
    print(f'lambda={best["lam"]}, u={best["u"]}, R_U={best["R_U"]}')
    print(f'a1={a1}, a2={a2}, tau={tau}')
    print(f'log2_work={best["free_nn_work"]:.12f}')
    print(f'rounded_log2_work={best["free_nn_work"]:.2f}')
    print(f'profiles={len(rows)}')
    print('tau_search=all' if args.all_tau else f'tau_search=representation center + {TAU_OFFSETS}, plus endpoints 0 and lambda')
    print('Model: free final matching and candidate verification; conditional Poisson success estimate.')
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open('x', newline='', encoding='utf-8') as handle:
            writer = csv.DictWriter(handle, fieldnames=['free_nn_work', 'lam', 'u', 'R_U', 'details'])
            writer.writeheader()
            writer.writerows(rows)
        print(f'Output: {args.output}')


if __name__ == '__main__':
    main()
