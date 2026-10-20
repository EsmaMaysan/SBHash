
import math
import csv
from dataclasses import dataclass, asdict
from typing import Iterable, List, Optional


def D_p(p: int, t: int) -> int:

    if p < 2:
        raise ValueError("p must be at least 2.")
    if t < 0:
        raise ValueError("t must be nonnegative.")
    return 1 + t * (p - 1) + math.comb(t, 2) * (p - 1) ** 2


def L_p(p: int, t: int) -> int:

    return D_p(p, t)


def log2_invertibility_probability(p: int, r: int) -> float:

    return sum(math.log2(1.0 - p ** (-j)) for j in range(1, r + 1))


def balanced_recovery_exponent(p: int, ell: int, h: int, rho: int):


    if h == 0:
        if rho != 0:
            raise ValueError("rho must be 0 when h=0.")
        return 0.0, 0, 0, 0.0

    if not (h <= rho <= h * ell):
        raise ValueError("rho is incompatible with h and ell.")

    f_L, b_L = divmod(rho, h)

    if f_L > ell or (b_L > 0 and f_L + 1 > ell):
        raise ValueError("Balanced allocation exceeds block length ell.")

    log2_R = (
        (h - b_L) * math.log2(L_p(p, f_L))
        + b_L * math.log2(L_p(p, f_L + 1))
    )

    E_rec = rho * math.log2(p) - log2_R

    return E_rec, f_L, b_L, log2_R


@dataclass
class HybridResult:
    p: int
    ell: int
    r: int
    m: int

    h: int
    rho: int
    nu: int

    residual_r: int
    residual_m: int

    f_L: int
    b_L: int

    blocks_per_smallest_list: int
    larger_initial_lists: int

    log2_recovery_factor: float
    recovery_exponent: float

    log2_list_capacity: float
    log2_Wagner_list_size: float

    time_exponent: float
    memory_list_elements_exponent: float
    memory_bits_exponent: float

    rank_penalty: float
    time_with_rank_exponent: float

    target_bits: float
    margin_time: float
    margin_time_with_rank: float


def hybrid_configuration(
    p: int,
    ell: int,
    r: int,
    m: int,
    h: int,
    rho: int,
    nu: int,
    target_bits: float = 128.0,
) -> Optional[HybridResult]:


    if not (0 <= h < m):
        return None

    if h == 0:
        if rho != 0:
            return None
    else:
        if not (h <= rho < r):
            return None
        if rho > h * ell:
            return None

    residual_r = r - rho
    residual_m = m - h

    if residual_r <= 0 or residual_m <= 0:
        return None

    if nu < 1:
        return None

    K = 2 ** nu

    if K > residual_m:
        return None

    g, c = divmod(residual_m, K)

    if g <= 0:
        return None


    try:
        E_rec, f_L, b_L, log2_R = balanced_recovery_exponent(
            p=p,
            ell=ell,
            h=h,
            rho=rho,
        )
    except ValueError:
        return None


    log2_Dell = math.log2(D_p(p, ell))
    log2_capacity = g * log2_Dell

    log2_NW = residual_r * math.log2(p) / (nu + 1)


    if log2_capacity + 1e-12 < log2_NW:
        return None

    time_exp = E_rec + nu + log2_NW


    memory_list_elements_exp = nu + log2_NW


    bits_per_field_element = math.ceil(math.log2(p))
    memory_bits_exp = (
        memory_list_elements_exp
        + math.log2(max(1, residual_r))
        + math.log2(bits_per_field_element)
    )

    rank_penalty = -log2_invertibility_probability(p, r)
    time_with_rank = time_exp + rank_penalty

    return HybridResult(
        p=p,
        ell=ell,
        r=r,
        m=m,
        h=h,
        rho=rho,
        nu=nu,
        residual_r=residual_r,
        residual_m=residual_m,
        f_L=f_L,
        b_L=b_L,
        blocks_per_smallest_list=g,
        larger_initial_lists=c,
        log2_recovery_factor=log2_R,
        recovery_exponent=E_rec,
        log2_list_capacity=log2_capacity,
        log2_Wagner_list_size=log2_NW,
        time_exponent=time_exp,
        memory_list_elements_exponent=memory_list_elements_exp,
        memory_bits_exponent=memory_bits_exp,
        rank_penalty=rank_penalty,
        time_with_rank_exponent=time_with_rank,
        target_bits=target_bits,
        margin_time=time_exp - target_bits,
        margin_time_with_rank=time_with_rank - target_bits,
    )


def optimize_hybrid(
    p: int,
    ell: int,
    r: int,
    m: int,
    target_bits: float = 128.0,
    top_k: int = 20,
    include_pure_wagner: bool = True,
    verbose: bool = True,
) -> List[HybridResult]:


    results = []
    tested = 0
    feasible = 0

    h_start = 0 if include_pure_wagner else 1

    for h in range(h_start, m):

        if h == 0:
            rho_values = [0]
        else:
            rho_min = h
            rho_max = min(h * ell, r - 1)
            if rho_min > rho_max:
                continue
            rho_values = range(rho_min, rho_max + 1)

        residual_m = m - h
        if residual_m < 2:
            continue

        max_nu = int(math.floor(math.log2(residual_m)))

        for rho in rho_values:
            for nu in range(1, max_nu + 1):
                tested += 1

                res = hybrid_configuration(
                    p=p,
                    ell=ell,
                    r=r,
                    m=m,
                    h=h,
                    rho=rho,
                    nu=nu,
                    target_bits=target_bits,
                )

                if res is not None:
                    feasible += 1
                    results.append(res)

        if verbose:
            print(
                f"h={h:4d}/{m-1} | "
                f"tested={tested:,} | feasible={feasible:,}",
                end="\r",
            )

    if verbose:
        print()

    results.sort(
        key=lambda z: (
            z.time_exponent,
            z.memory_list_elements_exponent,
            z.h,
            z.rho,
            z.nu,
        )
    )

    return results[:top_k]


def pure_wagner_results(
    p: int,
    ell: int,
    r: int,
    m: int,
    target_bits: float = 128.0,
):

    out = []
    for nu in range(1, int(math.floor(math.log2(m))) + 1):
        res = hybrid_configuration(
            p=p,
            ell=ell,
            r=r,
            m=m,
            h=0,
            rho=0,
            nu=nu,
            target_bits=target_bits,
        )
        if res is not None:
            out.append(res)

    out.sort(key=lambda z: z.time_exponent)
    return out


def print_results(results: List[HybridResult], title: Optional[str] = None):
    if title:
        print("\n" + title)

    print(
        f"{'time':>10} {'h':>5} {'rho':>5} {'nu':>4} "
        f"{'r-res':>6} {'m-res':>6} "
        f"{'Erec':>10} {'log2N':>10} "
        f"{'cap':>10} {'mem':>10}"
    )

    for z in results:
        print(
            f"{z.time_exponent:10.3f} "
            f"{z.h:5d} "
            f"{z.rho:5d} "
            f"{z.nu:4d} "
            f"{z.residual_r:6d} "
            f"{z.residual_m:6d} "
            f"{z.recovery_exponent:10.3f} "
            f"{z.log2_Wagner_list_size:10.3f} "
            f"{z.log2_list_capacity:10.3f} "
            f"{z.memory_list_elements_exponent:10.3f}"
        )


def save_results_csv(results: List[HybridResult], filename: str):
    if not results:
        raise ValueError("No results to save.")

    rows = [asdict(x) for x in results]

    with open(filename, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)

    print(f"Saved {len(rows)} rows to {filename}")


def compare_current_instance():


    p = 5
    ell = 64
    r = 528
    m = 192

    R = optimize_hybrid(
        p=p,
        ell=ell,
        r=r,
        m=m,
        target_bits=128,
        top_k=20,
        include_pure_wagner=True,
        verbose=True,
    )

    print_results(
        R,
        title="Hybrid linearization + generalized birthday -- working instance",
    )

    W = pure_wagner_results(
        p=p,
        ell=ell,
        r=r,
        m=m,
        target_bits=128,
    )

    print_results(
        W,
        title="Pure Wagner limiting configurations",
    )

    return R, W


if __name__ == "__main__":
    compare_current_instance()
