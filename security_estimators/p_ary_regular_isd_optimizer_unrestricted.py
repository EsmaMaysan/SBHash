import csv
import math
import heapq
import time
from dataclasses import dataclass, asdict
from functools import lru_cache
from typing import Optional

import numpy as np

NEG_INF = float("-inf")


def D_local(p: int, t: int, binary_fsb: bool = False) -> int:

    if binary_fsb:
        return 1 + t * (t - 1) // 2
    return 1 + t * (p - 1) + (t * (t - 1) // 2) * (p - 1) ** 2


def E_local(p: int, t: int, binary_fsb: bool = False) -> int:

    if binary_fsb:
        return t
    return 1 + t * (p - 1)


def log2_invertibility_probability(p: int, r: int) -> float:
    return sum(math.log2(1.0 - p ** (-j)) for j in range(1, r + 1))


def logsum2(values) -> float:
    values = [v for v in values if v != NEG_INF]
    if not values:
        return NEG_INF
    m = max(values)
    return m + math.log2(sum(2.0 ** (v - m) for v in values))


def log2_success_probability(log2_delta: float) -> float:

    if log2_delta < -40.0:
        return log2_delta
    if log2_delta > 6.0:
        return 0.0
    delta = 2.0 ** log2_delta
    return math.log2(-math.expm1(-delta))


@lru_cache(maxsize=None)
def _log2_binomials(n: int):
    vals = np.empty(n + 1, dtype=float)
    vals[0] = 0.0
    for k in range(1, n + 1):
        vals[k] = vals[k - 1] + math.log2(n - k + 1) - math.log2(k)
    return vals


@lru_cache(maxsize=200000)
def _normalized_type_polynomial(n: int, weight: float):

    if n == 0:
        return np.array([1.0], dtype=float), 0.0
    if weight == 0.0:
        arr = np.zeros(n + 1, dtype=float)
        arr[0] = 1.0
        return arr, 0.0

    logs = _log2_binomials(n) + np.arange(n + 1, dtype=float) * math.log2(weight)
    scale = float(np.max(logs))
    return np.exp2(logs - scale), scale


def _poly_logs(type_counts, p: int, binary_fsb: bool, weighted: bool):


    arr = np.array([1.0], dtype=float)
    scale = 0.0
    coefficient_factor = 1 if binary_fsb else (p - 1)

    for q, u, n in type_counts:
        base = coefficient_factor * u
        if weighted:
            base *= E_local(p, q, binary_fsb) / D_local(p, q, binary_fsb)

        poly, poly_scale = _normalized_type_polynomial(n, float(base))
        arr = np.convolve(arr, poly)
        scale += poly_scale

        peak = float(np.max(arr))
        if peak > 0.0:
            arr /= peak
            scale += math.log2(peak)

    logs = np.full(len(arr), -np.inf, dtype=float)
    mask = arr > 0.0
    logs[mask] = np.log2(arr[mask]) + scale
    return logs


def _half_types(ell: int, h: int, f: int, n_high_q: int, s_total: int):


    n_low_q = h - n_high_q
    types = []

    if s_total <= n_low_q:

        if s_total:
            types.append((f, ell - f - 1, s_total))
        if n_low_q - s_total:
            types.append((f, ell - f, n_low_q - s_total))
        if n_high_q:
            types.append((f + 1, ell - f - 1, n_high_q))
    else:


        remaining = s_total - n_low_q
        k, extra = divmod(remaining, h)

        low = max(0, extra - n_low_q)
        high = min(extra, n_high_q)
        target_high = round(extra * n_high_q / h) if h else 0
        extra_high = min(high, max(low, target_high))
        extra_low = extra - extra_high

        u0 = ell - (f + 1 + k)
        u1 = u0 - 1
        if u0 < 1 or (extra and u1 < 1):
            return None

        if n_low_q - extra_low:
            types.append((f, u0, n_low_q - extra_low))
        if extra_low:
            types.append((f, u1, extra_low))
        if n_high_q - extra_high:
            types.append((f + 1, u0, n_high_q - extra_high))
        if extra_high:
            types.append((f + 1, u1, extra_high))

    if any(u < 1 for _, u, _ in types):
        return None

    return tuple(sorted(types))


def balanced_layout_types(ell: int, r: int, w0: int, lam: int):


    if w0 % 2:
        return None
    if not (0 <= lam <= r):
        return None
    if r > w0 * (ell - 1):
        return None

    h = w0 // 2
    f, b = divmod(r - lam, w0)

    b_left = (b + 1) // 2
    b_right = b // 2
    lam_left = (lam + 1) // 2
    lam_right = lam // 2

    left = _half_types(ell, h, f, b_left, lam_left)
    right = _half_types(ell, h, f, b_right, lam_right)
    if left is None or right is None:
        return None

    return left, right, f, b


@dataclass
class ISDResult:
    log2_work: float
    w0: int
    x: int
    lam: int
    f: int
    b: int
    log2_N: float
    log2_delta: float
    log2_capacity: float
    log2_memory_bits: float
    log2_pinv: float


def optimize_log2_N(p, r, lam, x, log2_capacity,
                    log2_delta_constant, log2_pinv):


    z_sat = -0.5 * log2_delta_constant

    if log2_capacity <= z_sat:
        candidates = [log2_capacity]
    else:
        candidates = []
        for d in (-4.0, -3.0, -2.0, -1.5, -1.0, -0.5, 0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0):
            z = max(0.0, min(log2_capacity, z_sat + d))
            candidates.append(z)
        if log2_capacity - z_sat < 3.0:
            candidates.append(log2_capacity)

    best = None
    for z in set(candidates):
        log2_delta = 2.0 * z + log2_delta_constant
        log2_psucc = log2_success_probability(log2_delta)


        terms = [3.0 * math.log2(r)]


        if lam > 0:
            terms.append(log2_pinv + 1.0 + z + math.log2(lam))

        if r > lam:
            terms.append(
                log2_pinv + 2.0 * z - lam * math.log2(p)
                + math.log2(2.0 * x * (r - lam))
            )

        log2_cost_per_selection = logsum2(terms)
        log2_total_work = log2_cost_per_selection - log2_pinv - log2_psucc

        if best is None or log2_total_work < best[0]:
            best = (log2_total_work, z, log2_delta)

    return best


def _lambda_values(r: int, w0: int, ell: int, unrestricted: bool):
    if unrestricted:
        return range(0, r + 1)


    values = []
    for f in range(0, min(ell - 1, r // w0) + 1):
        lam = r - f * w0
        if 0 <= lam <= r:
            values.append(lam)
    return sorted(set(values))


def optimize_p_ary_regular_isd(
    p: int,
    ell: int,
    r: int,
    m: int,
    binary_fsb: bool = False,
    unrestricted: bool = True,
    top_k: int = 20,
    verbose: bool = True,
):


    if not binary_fsb and p <= 2:
        raise ValueError("For p=2 use binary_fsb=True.")

    log2_pinv = log2_invertibility_probability(p, r)
    log2p = math.log2(p)
    projective_correction = 0.0 if binary_fsb else math.log2(p - 1)

    w0_min = math.ceil(r / ell)
    if w0_min % 2:
        w0_min += 1
    w0_max = min(m, r)

    best_heap = []
    tested = 0
    layouts = 0
    counter = 0
    t0 = time.perf_counter()
    total_w0 = ((w0_max - w0_min) // 2) + 1
    w0_index = 0

    for w0 in range(w0_min, w0_max + 1, 2):
        w0_index += 1
        h = w0 // 2

        for lam in _lambda_values(r, w0, ell, unrestricted):
            layout = balanced_layout_types(ell, r, w0, lam)
            if layout is None:
                continue

            left, right, f, b = layout
            layouts += 1

            logC_L = _poly_logs(left, p, binary_fsb, weighted=False)
            logW_L = _poly_logs(left, p, binary_fsb, weighted=True)
            logC_R = _poly_logs(right, p, binary_fsb, weighted=False)
            logW_R = _poly_logs(right, p, binary_fsb, weighted=True)

            log2_D_all = (
                (w0 - b) * math.log2(D_local(p, f, binary_fsb))
                + b * math.log2(D_local(p, f + 1, binary_fsb))
            )

            for x in range(1, h + 1):
                if x >= len(logC_L) or x >= len(logC_R):
                    continue
                vals = (logC_L[x], logW_L[x], logC_R[x], logW_R[x])
                if not all(math.isfinite(float(v)) for v in vals):
                    continue

                tested += 1
                log2_capacity = min(float(logC_L[x]), float(logC_R[x]))


                log2_completion = (
                    log2_D_all
                    + (float(logW_L[x]) - float(logC_L[x]))
                    + (float(logW_R[x]) - float(logC_R[x]))
                )

                log2_delta_constant = (
                    log2_completion - r * log2p - projective_correction
                )

                work, log2_N, log2_delta = optimize_log2_N(
                    p, r, lam, x, log2_capacity,
                    log2_delta_constant, log2_pinv
                )

                bits_per_field = math.ceil(log2p)
                if lam > 0:
                    log2_memory = (
                        1.0 + log2_N + math.log2(lam)
                        + math.log2(bits_per_field)
                    )
                else:
                    log2_memory = 1.0 + log2_N

                result = ISDResult(
                    float(work), w0, x, lam, f, b,
                    float(log2_N), float(log2_delta),
                    float(log2_capacity), float(log2_memory),
                    float(log2_pinv)
                )

                counter += 1
                key = -result.log2_work
                if len(best_heap) < top_k:
                    heapq.heappush(best_heap, (key, counter, result))
                elif result.log2_work < -best_heap[0][0]:
                    heapq.heapreplace(best_heap, (key, counter, result))

        if verbose and (w0_index == 1 or w0_index % 5 == 0 or w0 == w0_max):
            elapsed = time.perf_counter() - t0
            pct = 100.0 * w0_index / total_w0
            print(
                f"w0={w0:4d}/{w0_max} | {pct:6.2f}% | "
                f"layouts={layouts:,} | configs={tested:,} | "
                f"elapsed={elapsed:7.1f}s",
                end="\r"
            )

    if verbose:
        print()

    results = [item[2] for item in best_heap]
    results.sort(key=lambda z: z.log2_work)
    return results


def print_results(results, title=None):
    if title:
        print("\n" + title)

    print(
        f"{'work':>10} {'w0':>5} {'x':>4} {'lambda':>7} "
        f"{'f':>4} {'b':>4} {'log2N':>10} {'log2delta':>11} "
        f"{'capacity':>10} {'memory':>10}"
    )
    for z in results:
        print(
            f"{z.log2_work:10.3f} {z.w0:5d} {z.x:4d} {z.lam:7d} "
            f"{z.f:4d} {z.b:4d} {z.log2_N:10.3f} "
            f"{z.log2_delta:11.3f} {z.log2_capacity:10.3f} "
            f"{z.log2_memory_bits:10.3f}"
        )


def save_results_csv(results, filename="p_ary_regular_isd_results.csv"):
    if not results:
        return
    fields = list(asdict(results[0]).keys())
    with open(filename, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        for row in results:
            writer.writerow(asdict(row))
    print(f"Saved: {filename}")


def validate_against_blps():
    tests = [
        ("FSB48",  2, 2**14,  192,  24,  66.31),
        ("FSB160", 2, 2**14,  640,  80, 196.70),
        ("FSB256", 2, 2**14, 1024, 128, 307.56),
    ]

    for name, p, ell, r, m, published in tests:
        best = optimize_p_ary_regular_isd(
            p, ell, r, m,
            binary_fsb=True,
            unrestricted=False,
            top_k=1,
            verbose=False,
        )[0]
        print(
            f"{name:7s}: log2 work={best.log2_work:.3f}, "
            f"published={published:.2f}, w0={best.w0}, x={best.x}, "
            f"log2 N={best.log2_N:.3f}, lambda={best.lam}"
        )


if __name__ == "__main__":
    validate_against_blps()
