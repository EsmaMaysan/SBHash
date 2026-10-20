
import math
from dataclasses import dataclass
from typing import Optional


def log2_binom(n: int, k: int) -> float:
    if k < 0 or k > n:
        return float("-inf")
    if k == 0 or k == n:
        return 0.0
    return (
        math.lgamma(n + 1)
        - math.lgamma(k + 1)
        - math.lgamma(n - k + 1)
    ) / math.log(2.0)


def binary_rep_depth2_cost(
    n: int,
    k: int,
    w: int,
    p_max: int = 40,
    eps_max: int = 32,
):


    if n <= 0 or k <= 0 or w <= 0 or k >= n:
        raise ValueError("Require 0 < k < n and w > 0.")

    beta = n // w
    r = n - k


    n_eff = beta * w
    k_eff = n_eff - r
    k_prime = k_eff - w

    if k_prime <= 0:
        raise ValueError("The binary Rep estimator requires k-w > 0.")

    best = None

    for p_weight in range(0, p_max, 4):
        for eps_x in range(0, eps_max, 2):
            p_x = p_weight / 2.0 + eps_x

            if w / 2.0 < p_weight / 2.0:
                continue


            half_w = round(w / 2)
            if p_x / 2.0 != int(p_x / 2.0):
                continue
            px_half = int(p_x / 2.0)
            if px_half > half_w:
                continue

            log2_L1_approx = (
                log2_binom(half_w, px_half)
                + (p_x / 2.0) * math.log2(k_prime)
            )

            if not math.isfinite(log2_L1_approx):
                continue


            if (p_weight // 2) % 2 != 0:
                continue

            a = p_weight // 2
            a2 = p_weight // 4
            if a2 > a:
                continue

            rem = int(round(w / 2 - p_weight / 2))
            eps_half = eps_x // 2
            if eps_half > rem:
                continue

            log2_R = 2.0 * (
                log2_binom(a, a2)
                + log2_binom(rem, eps_half)
            )

            ell_approx = math.ceil(2.0 * log2_L1_approx)
            ell_min = max(0, math.floor(0.5 * ell_approx))
            ell_max = max(ell_min + 1, math.floor(1.5 * ell_approx))

            for ell_match in range(ell_min, ell_max):
                v = (k_prime + ell_match) / w
                b = n_eff / w

                if v <= 0 or v >= b:
                    continue

                ell_x = math.floor(log2_R)

                log2_L1 = (
                    log2_binom(round(w / 2), px_half)
                    + (p_x / 2.0) * math.log2(v)
                )

                log2_Lx1 = 2.0 * log2_L1 - ell_x
                log2_Nx = 2.0 * log2_Lx1 - (ell_match - ell_x)


                pw_half = round(p_weight / 2)
                if pw_half > math.floor(w / 2) or pw_half > math.ceil(w / 2):
                    continue

                log2_p_iter = (
                    log2_binom(math.floor(w / 2), pw_half)
                    + log2_binom(math.ceil(w / 2), pw_half)
                    + p_weight * math.log2(v / b)
                    + (w - p_weight) * math.log2(1.0 - v / b)
                )


                log2_T_iter = (
                    math.log2(n_eff)
                    + max(
                        2.0 * math.log2(n_eff - k_prime),
                        2.0 + log2_L1,
                        1.0 + log2_Lx1,
                        log2_Nx,
                    )
                )

                cost = log2_T_iter - log2_p_iter
                memory = max(log2_L1, log2_Lx1) + math.log2(n_eff)

                if best is None or cost < best["time"]:
                    best = {
                        "time": cost,
                        "memory": memory,
                        "p_weight": p_weight,
                        "eps_x": eps_x,
                        "ell_x": ell_x,
                        "ell": ell_match,
                        "log2_R": log2_R,
                        "log2_L1": log2_L1,
                        "log2_Lx1": log2_Lx1,
                        "log2_Nx": log2_Nx,
                        "log2_p_iter": log2_p_iter,
                        "n_eff": n_eff,
                        "k_eff": k_eff,
                    }

    if best is None:
        raise RuntimeError(
            "No admissible parameters found. Increase p_max/eps_max "
            "or check the RSD instance."
        )

    return best


def gamma_size(p: int, ell: int) -> int:


    if p < 2 or ell <= 0:
        raise ValueError("Require p >= 2 and ell > 0.")
    return 1 + ell * (p - 1)


def rep_nonzero_local(p: int) -> int:


    if p < 2:
        raise ValueError("Require p >= 2.")
    return p


def rep_zero_local(p: int, ell: int) -> int:


    return gamma_size(p, ell)


@dataclass
class ParyRepresentationProfile:
    p: int
    ell: int
    active_blocks: int
    represented_zero_blocks: int
    nonzero_local_multiplicity: int
    zero_local_multiplicity: int
    log2_total_representation_multiplicity: float


def p_ary_representation_profile(
    p: int,
    ell: int,
    active_blocks: int,
    represented_zero_blocks: int = 0,
) -> ParyRepresentationProfile:


    if active_blocks < 0 or represented_zero_blocks < 0:
        raise ValueError("Block counts must be nonnegative.")

    rnz = rep_nonzero_local(p)
    rz = rep_zero_local(p, ell)

    log_mult = (
        active_blocks * math.log2(rnz)
        + represented_zero_blocks * math.log2(rz)
    )

    return ParyRepresentationProfile(
        p=p,
        ell=ell,
        active_blocks=active_blocks,
        represented_zero_blocks=represented_zero_blocks,
        nonzero_local_multiplicity=rnz,
        zero_local_multiplicity=rz,
        log2_total_representation_multiplicity=log_mult,
    )


def print_local_diagnostics(p: int, ell: int):
    print("=" * 72)
    print("Exact p-ary local representation diagnostics")
    print(f"p={p}, ell={ell}")
    print(f"|Gamma_ell|                     = {gamma_size(p, ell)}")
    print(f"R_Gamma(nonzero a e_j)          = {rep_nonzero_local(p)}")
    print(f"R_Gamma(0)                      = {rep_zero_local(p, ell)}")
    print(f"log2 R_Gamma(nonzero)           = {math.log2(rep_nonzero_local(p)):.6f}")
    print(f"log2 R_Gamma(0)                 = {math.log2(rep_zero_local(p, ell)):.6f}")
    print("=" * 72)


if __name__ == "__main__":

    print_local_diagnostics(p=5, ell=64)


    prof = p_ary_representation_profile(
        p=5,
        ell=64,
        active_blocks=120,
        represented_zero_blocks=0,
    )
    print()
    print("Example representation profile")
    print(prof)
