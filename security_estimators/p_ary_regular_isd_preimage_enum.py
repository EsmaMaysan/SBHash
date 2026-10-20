
import math
import csv
from dataclasses import dataclass, asdict
from typing import List, Optional

import numpy as np


def logadd2(a, b):
    m = np.maximum(a, b)
    return m + np.log2(np.exp2(a - m) + np.exp2(b - m))


def log2_rank_probability(p: int, r: int, lam: int) -> float:


    return sum(math.log2(1.0 - p ** (-k)) for k in range(lam + 1, r + 1))


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


@dataclass
class EnumResult:
    p: int
    ell: int
    r: int
    m: int

    lam: int
    u: int
    R_U: int

    log2_NL: float
    log2_NR: float
    log2_capacity_L: float
    log2_capacity_R: float

    log2_completion_factor: float
    log2_delta: float

    rank_penalty: float
    work_exponent: float
    memory_bits_exponent: float

    target_bits: float
    margin: float


def balanced_two_list_capacities(
    p: int,
    ell: int,
    u: int,
    R_U: np.ndarray,
):


    logpm1 = math.log2(p - 1)

    fU = R_U // u
    bU = R_U - u * fU
    aU = u - bU

    q1 = ell - fU
    q2 = q1 - 1

    logc1 = logpm1 + np.log2(q1.astype(float))

    logc2 = np.zeros_like(logc1)
    mask = bU > 0
    logc2[mask] = logpm1 + np.log2(q2[mask].astype(float))


    base = (aU // 2) * logc1 + (bU // 2) * logc2

    rem1 = aU % 2
    rem2 = bU % 2

    cap_small = base.copy()
    cap_large = base.copy()

    only1 = (rem1 == 1) & (rem2 == 0)
    only2 = (rem1 == 0) & (rem2 == 1)
    both = (rem1 == 1) & (rem2 == 1)

    cap_large[only1] += logc1[only1]
    cap_large[only2] += logc2[only2]


    cap_small[both] += np.minimum(logc1[both], logc2[both])
    cap_large[both] += np.maximum(logc1[both], logc2[both])

    return cap_small, cap_large


def completion_factor_logs(
    p: int,
    m: int,
    u: int,
    pivot_total: int,
    R_U: np.ndarray,
):


    v = m - u
    Rout = pivot_total - R_U

    if v == 0:
        return np.zeros_like(R_U, dtype=float)

    fV = Rout // v
    bV = Rout - v * fV

    return (
        v * math.log2(p - 1)
        + (v - bV) * np.log2(fV.astype(float))
        + bV * np.log2((fV + 1).astype(float))
    )


def optimize_list_sizes(
    p: int,
    r: int,
    lam: int,
    capL: np.ndarray,
    capR: np.ndarray,
    completion_log: np.ndarray,
    rank_log2: float,
):


    logp = math.log2(p)
    log_la = 3.0 * math.log2(r)

    cap_total = capL + capR


    s_target = r * logp - completion_log
    s_base = np.minimum(s_target, cap_total)

    best_total = np.full_like(capL, np.inf, dtype=float)
    best_x = np.zeros_like(capL)
    best_y = np.zeros_like(capL)
    best_delta = np.full_like(capL, -np.inf)
    best_mem = np.full_like(capL, np.inf)

    for offset in (-2.0, -1.0, 0.0, 1.0, 2.0):
        s = np.clip(s_base + offset, 0.0, cap_total)


        half = s / 2.0
        low = np.maximum(0.0, s - capR)
        high = np.minimum(capL, s)

        x = np.clip(half, low, high)
        y = s - x

        log2_delta = s + completion_log - r * logp
        log2_psucc = log2_success_from_delta(log2_delta)


        log2_list_sum = logadd2(x, y)


        if lam > 0:
            log2_list_cost = (
                rank_log2
                + log2_list_sum
                + math.log2(lam)
            )
        else:
            log2_list_cost = rank_log2 + log2_list_sum


        log2_matches = s - lam * logp

        if r > lam:
            log2_check_cost = (
                rank_log2
                + log2_matches
                + math.log2(r - lam)
            )
        else:
            log2_check_cost = rank_log2 + log2_matches


        M = np.maximum.reduce([
            np.full_like(s, log_la),
            log2_list_cost,
            log2_check_cost,
        ])

        log2_cost = M + np.log2(
            np.exp2(log_la - M)
            + np.exp2(log2_list_cost - M)
            + np.exp2(log2_check_cost - M)
        )


        total = log2_cost - rank_log2 - log2_psucc

        bits_per_field_element = math.ceil(math.log2(p))
        log2_memory_bits = (
            log2_list_sum
            + math.log2(max(1, lam))
            + math.log2(bits_per_field_element)
        )

        mask = total < best_total
        best_total[mask] = total[mask]
        best_x[mask] = x[mask]
        best_y[mask] = y[mask]
        best_delta[mask] = log2_delta[mask]
        best_mem[mask] = log2_memory_bits[mask]

    return best_total, best_x, best_y, best_delta, best_mem


def optimize_regular_isd_enum(
    p: int,
    ell: int,
    r: int,
    m: int,
    target_bits: float = 128.0,
    top_k: int = 20,
    verbose: bool = True,
) -> List[EnumResult]:


    if p <= 2:
        raise ValueError(
            "This coefficient-aware estimator is intended for p>2. "
            "The binary unit-valued RSD case needs separate local rules."
        )

    logp = math.log2(p)
    results: List[EnumResult] = []

    total_profiles = 0

    for lam in range(1, r):
        pivot_total = r - lam
        rank_log2 = log2_rank_probability(p, r, lam)
        rank_penalty = -rank_log2

        for u in range(2, m + 1):
            v = m - u

            if v == 0:

                if pivot_total > u * (ell - 1):
                    continue
                R_values = np.array([pivot_total], dtype=np.int64)
            else:


                lo = max(0, pivot_total - v * ell)
                hi = min(
                    pivot_total - v,
                    u * (ell - 1),
                )

                if lo > hi:
                    continue

                R_values = np.arange(lo, hi + 1, dtype=np.int64)

            total_profiles += len(R_values)

            capL, capR = balanced_two_list_capacities(
                p=p,
                ell=ell,
                u=u,
                R_U=R_values,
            )

            completion_log = completion_factor_logs(
                p=p,
                m=m,
                u=u,
                pivot_total=pivot_total,
                R_U=R_values,
            )

            (
                work,
                logNL,
                logNR,
                logdelta,
                membits,
            ) = optimize_list_sizes(
                p=p,
                r=r,
                lam=lam,
                capL=capL,
                capR=capR,
                completion_log=completion_log,
                rank_log2=rank_log2,
            )


            idx = int(np.argmin(work))

            results.append(
                EnumResult(
                    p=p,
                    ell=ell,
                    r=r,
                    m=m,
                    lam=lam,
                    u=u,
                    R_U=int(R_values[idx]),
                    log2_NL=float(logNL[idx]),
                    log2_NR=float(logNR[idx]),
                    log2_capacity_L=float(capL[idx]),
                    log2_capacity_R=float(capR[idx]),
                    log2_completion_factor=float(completion_log[idx]),
                    log2_delta=float(logdelta[idx]),
                    rank_penalty=float(rank_penalty),
                    work_exponent=float(work[idx]),
                    memory_bits_exponent=float(membits[idx]),
                    target_bits=target_bits,
                    margin=float(work[idx] - target_bits),
                )
            )

        if verbose and (lam % 10 == 0 or lam == r - 1):
            print(
                f"lambda={lam:4d}/{r-1} | "
                f"profiles evaluated={total_profiles:,}",
                end="\r",
            )

    if verbose:
        print()

    results.sort(
        key=lambda z: (
            z.work_exponent,
            z.memory_bits_exponent,
            z.lam,
            z.u,
        )
    )

    return results[:top_k]


def print_results(results: List[EnumResult], title: Optional[str] = None):
    if title:
        print("\n" + title)

    print(
        f"{'work':>10} {'lambda':>7} {'u':>5} {'R_U':>6} "
        f"{'log2NL':>10} {'log2NR':>10} "
        f"{'log2delta':>11} {'memory':>10}"
    )

    for z in results:
        print(
            f"{z.work_exponent:10.3f} "
            f"{z.lam:7d} "
            f"{z.u:5d} "
            f"{z.R_U:6d} "
            f"{z.log2_NL:10.3f} "
            f"{z.log2_NR:10.3f} "
            f"{z.log2_delta:11.3f} "
            f"{z.memory_bits_exponent:10.3f}"
        )


def save_results_csv(results: List[EnumResult], filename: str):
    if not results:
        raise ValueError("No results to save.")

    rows = [asdict(x) for x in results]

    with open(filename, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)

    print(f"Saved {len(rows)} rows to {filename}")


if __name__ == "__main__":
    R = optimize_regular_isd_enum(
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
        "p-ary Regular-ISD Enum -- current working instance"
    )

    save_results_csv(
        R,
        "p_ary_regular_isd_enum_results.csv"
    )
