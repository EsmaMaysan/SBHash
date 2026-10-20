
import math
import csv
from dataclasses import dataclass, asdict
from itertools import product
from typing import Iterable, List, Optional


def log2_invertibility_probability(p: int, r: int) -> float:

    return sum(math.log2(1.0 - p ** (-j)) for j in range(1, r + 1))


@dataclass
class RegularPrangeResult:
    p: int
    ell: int
    r: int
    m: int

    f: int
    b: int

    log2_supported_regular_vectors: float
    success_exponent: float

    rank_penalty: float
    selection_exponent: float

    cubic_la_overhead: float
    work_exponent_cubic: float

    target_bits: float
    margin_success: float
    margin_selection: float
    margin_work_cubic: float

    domain_log2: float
    codomain_log2: float
    mean_preimage_log2: float


def regular_prange_result(
    p: int,
    ell: int,
    r: int,
    m: int,
    target_bits: float = 128.0,
) -> RegularPrangeResult:

    if p < 2:
        raise ValueError("p must be at least 2.")
    if ell <= 0 or r <= 0 or m <= 0:
        raise ValueError("ell, r and m must be positive.")


    if r < m:
        raise ValueError("Regular-Prange requires r >= m.")


    if r > m * ell:
        raise ValueError("Impossible: r > m*ell.")

    f, b = divmod(r, m)

    if f < 1:
        raise ValueError("Every active block must contain at least one column.")
    if f > ell or (b > 0 and f + 1 > ell):
        raise ValueError("Balanced selection exceeds the block length ell.")


    log2_supported = (
        m * math.log2(p - 1)
        + (m - b) * math.log2(f)
        + (b * math.log2(f + 1) if b else 0.0)
    )


    success_exponent = r * math.log2(p) - log2_supported

    log2_pinv = log2_invertibility_probability(p, r)
    rank_penalty = -log2_pinv
    selection_exponent = success_exponent + rank_penalty

    cubic_la_overhead = 3.0 * math.log2(r)
    work_exponent_cubic = selection_exponent + cubic_la_overhead

    domain_log2 = m * math.log2(ell * (p - 1))
    codomain_log2 = r * math.log2(p)
    mean_preimage_log2 = domain_log2 - codomain_log2

    return RegularPrangeResult(
        p=p,
        ell=ell,
        r=r,
        m=m,
        f=f,
        b=b,
        log2_supported_regular_vectors=log2_supported,
        success_exponent=success_exponent,
        rank_penalty=rank_penalty,
        selection_exponent=selection_exponent,
        cubic_la_overhead=cubic_la_overhead,
        work_exponent_cubic=work_exponent_cubic,
        target_bits=target_bits,
        margin_success=success_exponent - target_bits,
        margin_selection=selection_exponent - target_bits,
        margin_work_cubic=work_exponent_cubic - target_bits,
        domain_log2=domain_log2,
        codomain_log2=codomain_log2,
        mean_preimage_log2=mean_preimage_log2,
    )


def print_result(res: RegularPrangeResult, title: Optional[str] = None):
    if title:
        print("\n" + title)

    print("=" * 72)
    print(f"p={res.p}, ell={res.ell}, r={res.r}, m={res.m}")
    print(f"Balanced selection: f={res.f}, b={res.b}")
    print(f"log2 supported regular vectors = {res.log2_supported_regular_vectors:.6f}")
    print(f"Success exponent               = {res.success_exponent:.6f}")
    print(f"Rank penalty                   = {res.rank_penalty:.6f}")
    print(f"Random-selection exponent      = {res.selection_exponent:.6f}")
    print(f"Cubic LA overhead              = {res.cubic_la_overhead:.6f}")
    print(f"Work exponent, O(r^3) model    = {res.work_exponent_cubic:.6f}")
    print()
    print(f"log2 |S|                       = {res.domain_log2:.6f}")
    print(f"log2 |F_p^r|                   = {res.codomain_log2:.6f}")
    print(f"log2 mean regular preimages    = {res.mean_preimage_log2:.6f}")
    print()
    print(f"Margin over {res.target_bits:.0f}-bit target:")
    print(f"  success exponent : {res.margin_success:+.6f} bits")
    print(f"  incl. rank       : {res.margin_selection:+.6f} bits")
    print(f"  incl. O(r^3)     : {res.margin_work_cubic:+.6f} bits")
    print("=" * 72)


def brute_force_balance_check(p: int, ell: int, r: int, m: int):


    if m > 8 or ell > 10:
        raise ValueError("Brute-force validation is intended only for small cases.")

    best_prod = -1
    best_patterns = []

    for tup in product(range(1, ell + 1), repeat=m):
        if sum(tup) != r:
            continue

        prod_t = math.prod(tup)

        if prod_t > best_prod:
            best_prod = prod_t
            best_patterns = [tup]
        elif prod_t == best_prod:
            best_patterns.append(tup)

    f, b = divmod(r, m)
    balanced = tuple(sorted([f] * (m - b) + [f + 1] * b))
    balanced_prod = math.prod(balanced)

    print("Brute-force balance check")
    print(f"p={p}, ell={ell}, r={r}, m={m}")
    print(f"Best product      = {best_prod}")
    print(f"Balanced product  = {balanced_prod}")
    print(f"Balanced pattern  = {balanced}")
    print(f"Validation        = {best_prod == balanced_prod}")

    return best_prod == balanced_prod


def scan_parameters(
    p: int,
    ell: int,
    r_values: Iterable[int],
    m_values: Iterable[int],
    target_bits: float = 128.0,
    require_r_gt_2m: bool = True,
) -> List[RegularPrangeResult]:

    results = []

    for r in r_values:
        for m in m_values:

            if require_r_gt_2m and r <= 2 * m:
                continue

            if r < m or r > m * ell:
                continue

            try:
                results.append(
                    regular_prange_result(
                        p=p,
                        ell=ell,
                        r=r,
                        m=m,
                        target_bits=target_bits,
                    )
                )
            except ValueError:
                pass

    results.sort(key=lambda z: (z.success_exponent, z.r, z.m))
    return results


def save_results_csv(results: List[RegularPrangeResult], filename: str):
    if not results:
        raise ValueError("No results to save.")

    rows = [asdict(x) for x in results]

    with open(filename, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)

    print(f"Saved {len(rows)} rows to {filename}")


if __name__ == "__main__":


    brute_force_balance_check(
        p=5,
        ell=4,
        r=8,
        m=3,
    )


    current = regular_prange_result(
        p=5,
        ell=64,
        r=528,
        m=192,
        target_bits=128,
    )

    print_result(
        current,
        title="p-ary regular-Prange -- current working instance"
    )
