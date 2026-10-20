
import math
import csv
from dataclasses import dataclass, asdict
from typing import List, Optional

import numpy as np


NEG_INF = -np.inf


def logadd2_scalar(a: float, b: float) -> float:
    if not math.isfinite(a):
        return b
    if not math.isfinite(b):
        return a
    m = max(a, b)
    return m + math.log2(2.0 ** (a - m) + 2.0 ** (b - m))


def logadd2_vec(a, b):
    a = np.asarray(a, dtype=float)
    b = np.asarray(b, dtype=float)
    m = np.maximum(a, b)
    out = np.full_like(m, -np.inf)

    finite = np.isfinite(m)
    if np.any(finite):
        out[finite] = m[finite] + np.log2(
            np.exp2(a[finite] - m[finite])
            + np.exp2(b[finite] - m[finite])
        )
    return out


def log_poly_linear_factors(a_values, b_values):


    n = len(a_values)
    coeff = np.full(n + 1, -np.inf, dtype=float)
    coeff[0] = 0.0

    degree = 0
    for aa, bb in zip(a_values, b_values):
        la = math.log2(aa) if aa > 0 else -math.inf
        lb = math.log2(bb) if bb > 0 else -math.inf

        new = np.full(n + 1, -np.inf, dtype=float)


        if math.isfinite(la):
            new[:degree + 1] = coeff[:degree + 1] + la


        if math.isfinite(lb):
            shifted = coeff[:degree + 1] + lb
            current = new[1:degree + 2]
            new[1:degree + 2] = logadd2_vec(current, shifted)

        coeff = new
        degree += 1

    return coeff


def log2_rank_probability(p: int, r: int, lam: int) -> float:


    return sum(
        math.log2(1.0 - p ** (-j))
        for j in range(lam + 1, r + 1)
    )


def log2_success_from_delta(log2_delta):
    x = np.asarray(log2_delta, dtype=float)
    out = np.empty_like(x)

    small = x < -40.0
    large = x > 6.0
    middle = ~(small | large)

    out[small] = x[small]
    out[large] = 0.0

    if np.any(middle):
        delta = np.exp2(x[middle])
        out[middle] = np.log2(-np.expm1(-delta))

    return out


def balanced_pivot_profile(ell: int, r: int, m: int, lam: int):


    total = r - lam
    if total < 0 or total > m * ell:
        return None

    f, b = divmod(total, m)
    if f > ell or (b and f + 1 > ell):
        return None

    t = np.array(
        [f + 1] * b + [f] * (m - b),
        dtype=np.int64,
    )


    order = np.argsort(np.arange(m) % 2 + 1e-6 * np.arange(m))

    high = [f + 1] * b
    low = [f] * (m - b)
    seq = []
    while high or low:
        if high:
            seq.append(high.pop())
        if low:
            seq.append(low.pop())
    t = np.array(seq[:m], dtype=np.int64)

    q = ell - t
    return t, q


def split_balanced(t, q):


    idxL = np.arange(len(t)) % 2 == 0
    idxR = ~idxL
    return (t[idxL], q[idxL]), (t[idxR], q[idxR])


def half_polynomials(p: int, t, q):


    c = (p - 1) * np.asarray(q, dtype=float)
    d = (p - 1) * np.asarray(t, dtype=float)

    C = log_poly_linear_factors(
        np.ones_like(c),
        c,
    )

    W = log_poly_linear_factors(
        d,
        c,
    )

    return C, W


@dataclass
class UnrestrictedEnumResult:
    p: int
    ell: int
    r: int
    m: int

    lam: int
    uL: int
    uR: int
    u: int

    log2_NL: float
    log2_NR: float
    log2_capacity_L: float
    log2_capacity_R: float

    log2_weighted_L: float
    log2_weighted_R: float

    log2_delta: float
    rank_penalty: float

    work_exponent: float
    memory_bits_exponent: float

    target_bits: float
    margin: float


def optimize_list_sizes_grid(
    p: int,
    r: int,
    lam: int,
    capL,
    capR,
    weightedL,
    weightedR,
    rank_log2: float,
):


    logp = math.log2(p)

    CL = capL[:, None]
    CR = capR[None, :]
    WL = weightedL[:, None]
    WR = weightedR[None, :]

    valid = (
        np.isfinite(CL)
        & np.isfinite(CR)
        & np.isfinite(WL)
        & np.isfinite(WR)
    )

    density = WL + WR - CL - CR - r * logp

    cap_total = CL + CR
    s_target = -density
    s_base = np.minimum(np.maximum(s_target, 0.0), cap_total)

    best_total = np.full_like(density, np.inf)
    best_x = np.zeros_like(density)
    best_y = np.zeros_like(density)
    best_delta = np.full_like(density, -np.inf)
    best_mem = np.full_like(density, np.inf)

    log_la = 3.0 * math.log2(r)
    bits_per_field_element = math.ceil(math.log2(p))

    for offset in (-2.0, -1.0, 0.0, 1.0, 2.0):
        s = np.minimum(
            np.maximum(s_base + offset, 0.0),
            cap_total,
        )

        half = s / 2.0
        low = np.maximum(0.0, s - CR)
        high = np.minimum(CL, s)

        x = np.minimum(np.maximum(half, low), high)
        y = s - x

        logdelta = s + density
        logpsucc = log2_success_from_delta(logdelta)

        log_list_sum = logadd2_vec(x, y)

        if lam > 0:
            log_list_cost = (
                rank_log2
                + log_list_sum
                + math.log2(lam)
            )
        else:
            log_list_cost = rank_log2 + log_list_sum

        log_matches = s - lam * logp

        if r > lam:
            log_check_cost = (
                rank_log2
                + log_matches
                + math.log2(r - lam)
            )
        else:
            log_check_cost = rank_log2 + log_matches

        M = np.maximum.reduce([
            np.full_like(s, log_la),
            log_list_cost,
            log_check_cost,
        ])

        log_cost = M + np.log2(
            np.exp2(log_la - M)
            + np.exp2(log_list_cost - M)
            + np.exp2(log_check_cost - M)
        )

        total = log_cost - rank_log2 - logpsucc
        total[~valid] = np.inf

        log_mem = (
            log_list_sum
            + math.log2(max(1, lam))
            + math.log2(bits_per_field_element)
        )

        mask = total < best_total
        best_total[mask] = total[mask]
        best_x[mask] = x[mask]
        best_y[mask] = y[mask]
        best_delta[mask] = logdelta[mask]
        best_mem[mask] = log_mem[mask]

    return best_total, best_x, best_y, best_delta, best_mem


def optimize_unrestricted_enum(
    p: int,
    ell: int,
    r: int,
    m: int,
    target_bits: float = 128.0,
    top_k: int = 20,
    verbose: bool = True,
) -> List[UnrestrictedEnumResult]:

    results: List[UnrestrictedEnumResult] = []

    for lam in range(1, r):
        prof = balanced_pivot_profile(
            ell=ell,
            r=r,
            m=m,
            lam=lam,
        )
        if prof is None:
            continue

        t, q = prof
        (tL, qL), (tR, qR) = split_balanced(t, q)

        CL, WL = half_polynomials(p, tL, qL)
        CR, WR = half_polynomials(p, tR, qR)

        rank_log2 = log2_rank_probability(p, r, lam)
        rank_penalty = -rank_log2

        (
            work,
            NL,
            NR,
            logdelta,
            memory,
        ) = optimize_list_sizes_grid(
            p=p,
            r=r,
            lam=lam,
            capL=CL,
            capR=CR,
            weightedL=WL,
            weightedR=WR,
            rank_log2=rank_log2,
        )


        flat = work.ravel()
        finite_idx = np.flatnonzero(np.isfinite(flat))

        if finite_idx.size == 0:
            continue

        keep = min(5, finite_idx.size)
        local = finite_idx[
            np.argpartition(flat[finite_idx], keep - 1)[:keep]
        ]

        for ind in local:
            uL, uR = np.unravel_index(ind, work.shape)

            results.append(
                UnrestrictedEnumResult(
                    p=p,
                    ell=ell,
                    r=r,
                    m=m,
                    lam=lam,
                    uL=int(uL),
                    uR=int(uR),
                    u=int(uL + uR),
                    log2_NL=float(NL[uL, uR]),
                    log2_NR=float(NR[uL, uR]),
                    log2_capacity_L=float(CL[uL]),
                    log2_capacity_R=float(CR[uR]),
                    log2_weighted_L=float(WL[uL]),
                    log2_weighted_R=float(WR[uR]),
                    log2_delta=float(logdelta[uL, uR]),
                    rank_penalty=float(rank_penalty),
                    work_exponent=float(work[uL, uR]),
                    memory_bits_exponent=float(memory[uL, uR]),
                    target_bits=target_bits,
                    margin=float(work[uL, uR] - target_bits),
                )
            )

        if verbose and (lam % 25 == 0 or lam == r - 1):
            best_lam = np.nanmin(work)
            print(
                f"lambda={lam:4d}/{r-1} | "
                f"best work at lambda={best_lam:.3f}",
                end="\r",
            )

    if verbose:
        print()

    results.sort(
        key=lambda z: (
            z.work_exponent,
            z.memory_bits_exponent,
            z.lam,
        )
    )

    return results[:top_k]


def print_results(results: List[UnrestrictedEnumResult], title: Optional[str] = None):
    if title:
        print("\n" + title)

    print(
        f"{'work':>10} {'lambda':>7} {'uL':>5} {'uR':>5} {'u':>5} "
        f"{'log2NL':>10} {'log2NR':>10} "
        f"{'delta':>10} {'memory':>10}"
    )

    for z in results:
        print(
            f"{z.work_exponent:10.3f} "
            f"{z.lam:7d} "
            f"{z.uL:5d} "
            f"{z.uR:5d} "
            f"{z.u:5d} "
            f"{z.log2_NL:10.3f} "
            f"{z.log2_NR:10.3f} "
            f"{z.log2_delta:10.3f} "
            f"{z.memory_bits_exponent:10.3f}"
        )


def save_results_csv(results: List[UnrestrictedEnumResult], filename: str):
    if not results:
        raise ValueError("No results to save.")

    rows = [asdict(x) for x in results]

    with open(filename, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)

    print(f"Saved {len(rows)} rows to {filename}")


if __name__ == "__main__":
    R = optimize_unrestricted_enum(
        p=5,
        ell=64,
        r=528,
        m=192,
        target_bits=128,
        top_k=20,
        verbose=True,
    )

    print_results(
        R,
        "Unrestricted p-ary Regular-ISD Enum -- current working instance"
    )

    save_results_csv(
        R,
        "p_ary_regular_isd_enum_unrestricted_results.csv"
    )
