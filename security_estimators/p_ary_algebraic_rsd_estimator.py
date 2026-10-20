
import math
import csv
from dataclasses import dataclass, asdict
from typing import List, Optional


@dataclass
class AlgebraicResult:
    p: int
    ell: int
    r: int
    m: int

    guessed_zero_positions_per_block: int
    effective_ell: int

    solving_degree: int
    log2_M_D: float

    guessing_exponent: float

    dense_f4_exponent_omega2: float
    dense_f4_exponent_omega23728596: float
    dense_f4_exponent_omega3: float

    total_exponent_omega2: float
    total_exponent_omega23728596: float
    total_exponent_omega3: float

    dense_memory_exponent: float
    sparse_memory_exponent_field_elements: float


def poly_mul_small(poly, factor):

    out = [0] * (len(poly) + len(factor) - 1)
    for i, a in enumerate(poly):
        if a == 0:
            continue
        for j, b in enumerate(factor):
            if b:
                out[i + j] += a * b
    return out


def poly_power_small(factor, exponent):


    out = [1]
    for _ in range(exponent):
        out = poly_mul_small(out, factor)
    return out


def structural_polynomial(p: int, ell: int):


    if p < 2:
        raise ValueError("p must be >= 2.")
    if ell < 1:
        raise ValueError("ell must be >= 1.")

    coeff = [1]


    for _ in range(1, p - 1):
        coeff.append(ell)


    coeff.append(ell - 1)

    return coeff


def multiply_by_one_minus_x_power(poly, r):


    binom = [((-1) ** j) * math.comb(r, j) for j in range(r + 1)]

    out = [0] * (len(poly) + r)
    for i, a in enumerate(poly):
        if a == 0:
            continue
        for j, b in enumerate(binom):
            if b:
                out[i + j] += a * b

    return out


def hilbert_coefficient_from_A(A, p, r, degree):


    k_min = max(
        0,
        (degree - (len(A) - 1) + p - 1) // p,
    )
    k_max = degree // p

    value = 0

    for k in range(k_min, k_max + 1):
        idx = degree - p * k
        if 0 <= idx < len(A):
            value += math.comb(r + k - 1, k) * A[idx]

    return value


def solving_degree_and_structural_coeffs(
    p: int,
    ell: int,
    r: int,
    m: int,
    max_degree: Optional[int] = None,
):


    G = structural_polynomial(p, ell)
    P = poly_power_small(G, m)
    A = multiply_by_one_minus_x_power(P, r)

    if max_degree is None:


        max_degree = max(4 * len(P), 4 * r, 100)

    for d in range(max_degree + 1):
        c = hilbert_coefficient_from_A(A, p, r, d)

        if c <= 0:
            M_D = P[d] if d < len(P) else 0
            return d, M_D, P

    raise RuntimeError(
        f"No nonpositive Hilbert coefficient found up to degree {max_degree}."
    )


def log2_positive_integer(x: int) -> float:
    if x <= 0:
        return float("-inf")


    return math.log2(x)


def evaluate_guess(
    p: int,
    ell: int,
    r: int,
    m: int,
    g: int,
) -> AlgebraicResult:


    if not (0 <= g < ell):
        raise ValueError("Require 0 <= g < ell.")

    ell_eff = ell - g

    D, M_D, _ = solving_degree_and_structural_coeffs(
        p=p,
        ell=ell_eff,
        r=r,
        m=m,
    )

    if M_D <= 0:
        raise RuntimeError(
            "The predicted solving degree lies outside the support of "
            "the structural Hilbert polynomial; the current cost model "
            "is not applicable to this point."
        )

    logM = log2_positive_integer(M_D)

    if g == 0:
        Eguess = 0.0
    else:
        Eguess = -m * math.log2(1.0 - g / ell)

    omega2 = 2.0 * logM
    omega237 = 2.3728596 * logM
    omega3 = 3.0 * logM

    return AlgebraicResult(
        p=p,
        ell=ell,
        r=r,
        m=m,
        guessed_zero_positions_per_block=g,
        effective_ell=ell_eff,
        solving_degree=D,
        log2_M_D=logM,
        guessing_exponent=Eguess,
        dense_f4_exponent_omega2=omega2,
        dense_f4_exponent_omega23728596=omega237,
        dense_f4_exponent_omega3=omega3,
        total_exponent_omega2=Eguess + omega2,
        total_exponent_omega23728596=Eguess + omega237,
        total_exponent_omega3=Eguess + omega3,
        dense_memory_exponent=2.0 * logM,
        sparse_memory_exponent_field_elements=logM,
    )


def optimize_one_round_guessing(
    p: int,
    ell: int,
    r: int,
    m: int,
) -> List[AlgebraicResult]:


    results = []

    for g in range(ell):
        try:
            z = evaluate_guess(
                p=p,
                ell=ell,
                r=r,
                m=m,
                g=g,
            )
            results.append(z)
        except RuntimeError:
            pass

    results.sort(
        key=lambda z: (
            z.total_exponent_omega2,
            z.total_exponent_omega23728596,
            z.guessed_zero_positions_per_block,
        )
    )

    return results


def print_top(results: List[AlgebraicResult], k=15, title=None):
    if title:
        print("\n" + title)

    print(
        f"{'g':>4} {'ell_eff':>7} {'D':>5} "
        f"{'log2M':>10} {'guess':>10} "
        f"{'E(w=2)':>10} {'E(w=2.373)':>12} "
        f"{'mem-dense':>11}"
    )

    for z in results[:k]:
        print(
            f"{z.guessed_zero_positions_per_block:4d} "
            f"{z.effective_ell:7d} "
            f"{z.solving_degree:5d} "
            f"{z.log2_M_D:10.3f} "
            f"{z.guessing_exponent:10.3f} "
            f"{z.total_exponent_omega2:10.3f} "
            f"{z.total_exponent_omega23728596:12.3f} "
            f"{z.dense_memory_exponent:11.3f}"
        )


def save_csv(results: List[AlgebraicResult], filename):
    if not results:
        raise ValueError("No results.")

    rows = [asdict(x) for x in results]

    with open(filename, "w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)

    print(f"Saved: {filename}")


def small_identity_validation():


    tests = [
        (2, 3, 2, 2),
        (3, 3, 3, 2),
        (5, 2, 3, 2),
    ]

    ok = True

    for p, ell, r, m in tests:
        G = structural_polynomial(p, ell)
        P = poly_power_small(G, m)


        Phi = [1] * p
        Den = poly_power_small(Phi, r)


        direct = []
        maxd = 20

        for n in range(maxd + 1):
            rhs = P[n] if n < len(P) else 0

            for j in range(1, min(n, len(Den) - 1) + 1):
                rhs -= Den[j] * direct[n - j]

            direct.append(rhs)

        A = multiply_by_one_minus_x_power(P, r)
        fast = [
            hilbert_coefficient_from_A(A, p, r, n)
            for n in range(maxd + 1)
        ]

        good = direct == fast
        ok &= good

        print(
            f"(p={p}, ell={ell}, r={r}, m={m}) "
            f"identity check = {good}"
        )

    print("All identity checks passed:", ok)
    return ok


if __name__ == "__main__":
    small_identity_validation()

    R = optimize_one_round_guessing(
        p=5,
        ell=64,
        r=528,
        m=192,
    )

    print_top(
        R,
        k=20,
        title=(
            "p-ary algebraic RSD -- one-round Hilbert-series estimator "
            "(working instance)"
        ),
    )

    save_csv(
        R,
        "p_ary_algebraic_rsd_results.csv",
    )
