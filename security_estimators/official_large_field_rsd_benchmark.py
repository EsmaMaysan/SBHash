


import math
from dataclasses import dataclass
from typing import Optional, Tuple, List


def _log2sum(values):
    vals = [x for x in values if math.isfinite(x)]
    if not vals:
        return math.inf
    M = max(vals)
    return M + math.log2(sum(2.0 ** (x - M) for x in vals))


def degree_conj_for_q(n: int, k: int, h: int, f: int, mu: int) -> int:
    beta = n // h

    a1 = -(n - k - h)
    a2 = (n - k - h) * (n - k - h - 1) / 2
    a3 = -(n - k - h) * (n - k - h - 1) * (n - k - h - 2) / 6
    a4 = (
        (n - k - h) * (n - k - h - 1)
        * (n - k - h - 2) * (n - k - h - 3) / 24
    )

    b1 = (beta - mu - 1) * f
    b2 = (beta - mu - 1) ** 2 * f * (f - 1) / 2
    b3 = (beta - mu - 1) ** 3 * f * (f - 1) * (f - 2) / 6
    b4 = (beta - mu - 1) ** 4 * f * (f - 1) * (f - 2) * (f - 3) / 24

    c1 = (beta - 1) * (h - f)
    c2 = (beta - 1) ** 2 * (h - f) * (h - f - 1) / 2
    c3 = (
        (beta - 1) ** 3 * (h - f) * (h - f - 1)
        * (h - f - 2) / 6
    )
    c4 = (
        (beta - 1) ** 4 * (h - f) * (h - f - 1)
        * (h - f - 2) * (h - f - 3) / 24
    )

    d2 = a1*b1 + a1*c1 + b1*c1 + a2 + b2 + c2
    d3 = (
        c3 + b1*c2 + b2*c1 + b3
        + a1*(b1*c1 + b2 + c2)
        + a2*(b1 + c1) + a3
    )
    d4 = (
        c4 + b1*c3 + b2*c2 + b3*c1 + b4
        + a1*(b1*c2 + b2*c1 + b3 + c3)
        + a2*(b2 + c2 + b1*c1)
        + a3*(b1 + c1) + a4
    )

    if d2 < 1:
        return 2
    if d2 + d3 < 1:
        return 3
    if d2 + d3 + d4 < 1:
        return 4
    return 30


def _M1_values_for_q(n: int, k: int, h: int, f: int, mu: int):
    beta = n // h

    a1 = (beta - mu - 1) * f
    a2 = (beta - mu - 1) ** 2 * f * (f - 1) / 2
    a3 = (beta - mu - 1) ** 3 * f * (f - 1) * (f - 2) / 6
    a4 = (beta - mu - 1) ** 4 * f * (f - 1) * (f - 2) * (f - 3) / 24

    b1 = (beta - 1) * (h - f)
    b2 = (beta - 1) ** 2 * (h - f) * (h - f - 1) / 2
    b3 = (
        (beta - 1) ** 3 * (h - f) * (h - f - 1)
        * (h - f - 2) / 6
    )
    b4 = (
        (beta - 1) ** 4 * (h - f) * (h - f - 1)
        * (h - f - 2) * (h - f - 3) / 24
    )

    c1 = h - 1
    c2 = h * (h - 1) / 2
    c3 = (h + 1) * h * (h - 1) / 6
    c4 = (h + 2) * (h + 1) * h * (h - 1) / 24

    d2 = a1 + b1 + c1 + a1*b1 + a1*c1 + b1*c1 + a2 + b2 + c2
    d3 = (
        c3 + b1*c2 + b2*c1 + b3
        + a1*(b1*c1 + b2 + c2)
        + a2*(b1 + c1) + a3
    )
    d4 = (
        c4 + b1*c3 + b2*c2 + b3*c1 + b4
        + a1*(b1*c2 + b2*c1 + b3 + c3)
        + a2*(b2 + c2 + b1*c1)
        + a3*(b1 + c1) + a4
    )
    return [d2, d2+d3, d2+d3+d4]


def _M2_values_for_q(n: int, k: int, h: int, f: int, mu: int):
    beta = n // h

    a1 = -(n - k - h)
    a2 = (n - k - h) * (n - k - h - 1) / 2
    a3 = -(n - k - h) * (n - k - h - 1) * (n - k - h - 2) / 6
    a4 = (
        (n - k - h) * (n - k - h - 1)
        * (n - k - h - 2) * (n - k - h - 3) / 24
    )

    b1 = (beta - mu - 1) * f
    b2 = (beta - mu - 1) ** 2 * f * (f - 1) / 2
    b3 = (beta - mu - 1) ** 3 * f * (f - 1) * (f - 2) / 6
    b4 = (beta - mu - 1) ** 4 * f * (f - 1) * (f - 2) * (f - 3) / 24

    c1 = (beta - 1) * (h - f)
    c2 = (beta - 1) ** 2 * (h - f) * (h - f - 1) / 2
    c3 = (
        (beta - 1) ** 3 * (h - f) * (h - f - 1)
        * (h - f - 2) / 6
    )
    c4 = (
        (beta - 1) ** 4 * (h - f) * (h - f - 1)
        * (h - f - 2) * (h - f - 3) / 24
    )

    d2 = a1*b1 + a1*c1 + b1*c1 + a2 + b2 + c2
    d3 = (
        c3 + b1*c2 + b2*c1 + b3
        + a1*(b1*c1 + b2 + c2)
        + a2*(b1 + c1) + a3
    )
    d4 = (
        c4 + b1*c3 + b2*c2 + b3*c1 + b4
        + a1*(b1*c2 + b2*c1 + b3 + c3)
        + a2*(b2 + c2 + b1*c1)
        + a3*(b1 + c1) + a4
    )

    return [max(d2, 1), max(d2+d3, 1), max(d2+d3+d4, 1)]


@dataclass
class AGB2Point:
    cost: float
    f: int
    mu: int
    degree: int
    second_f: Optional[int] = None
    second_mu: Optional[int] = None


def _sub_agb2_for_q(n: int, k: int, h: int, f: int, mu: int,
                    repeat: int = 10) -> AGB2Point:


    d = degree_conj_for_q(n, k, h, f, mu)
    if d > 4:
        return AGB2Point(999999.0, f, mu, d)

    beta = n // h
    idx = d - 2

    M2_base = _M2_values_for_q(n, k, h, f, mu)[idx]

    best = 999999.0
    best_pair = (None, None)


    if M2_base < 2:
        M1s = _M1_values_for_q(n, k, h, f, mu)[idx]
        M1 = 3.0 * (k + 1 - f*mu) * (M1s ** 2)
        prob = 1.0 - mu / beta
        if M1 > 0 and prob > 0:
            best = math.log2(M1) - f*math.log2(prob)

    subg_best = 1.0e10
    stepg = repeat * 3

    for g in range(f*mu, -1, -1):
        if subg_best > best - 0.01:
            stepg -= 1
        else:
            stepg = repeat * 3

        if stepg < 0:
            break

        best = min(best, subg_best)
        subg_best = 1.0e10
        step = repeat

        for fp in range(f, 0, -1):
            if step < 0:
                break
            if g / fp > fp:
                break

            if g % fp != 0:
                continue

            mup = g // fp
            if mup > mu:
                continue

            step -= 1
            if fp <= 1:
                continue

            sM1 = _M1_values_for_q(n, k, h, fp, mup)[idx]
            sM2 = _M2_values_for_q(n, k, h, fp, mup)[idx]
            if sM1 <= 0 or sM2 <= 0:
                continue

            logM1 = math.log2(5.64) + 2.8*math.log2(sM1)
            logM2 = math.log2(5.64) + 2.8*math.log2(sM2)

            mm = max(sM1 - sM2, 1.0)


            if mm > 1.0:
                logM11 = (
                    math.log2(sM1)
                    + 2.0*math.log2(mm)
                    - math.log2(math.log2(mm))
                )
                logM1 = min(logM1, logM11)

            if sM2 > mm:
                logM2 = math.log2(5.64) + 2.8*math.log2(mm)

            prob1 = 1.0 - mup / beta
            prob2 = 1.0 - mu / beta
            if prob1 <= 0 or prob2 <= 0:
                continue

            logT1 = logM1 - fp*math.log2(prob1)
            logT2 = logM2 - f*math.log2(prob2)
            subcost = _log2sum([logT1, logT2])

            if subcost < subg_best:
                subg_best = subcost

            if subcost < best:
                best_pair = (fp, mup)

    best = min(best, subg_best)
    return AGB2Point(best, f, mu, d, best_pair[0], best_pair[1])


def agb2_large_field_benchmark(n: int, k: int, h: int):


    beta = n // h
    candidates: List[AGB2Point] = []

    for f in range(h + 1):
        if f == 0:
            mus = [0]
        else:
            mus = range(min(k // f, beta - 1), -1, -1)

        for mu in mus:
            d = degree_conj_for_q(n, k, h, f, mu)
            if d <= 4:
                candidates.append(_sub_agb2_for_q(n, k, h, f, mu))

    candidates.sort(key=lambda z: z.cost)
    return candidates


@dataclass
class HybridPoint:
    cost: float
    u: int
    q: int
    f: int
    n0: int
    beta: int


def hybrid_large_field_benchmark(n: int, k: int, h: int):


    beta = n // h


    r = n - k
    n = beta*h
    k = n - r

    gauss_constant = 2.8
    best = HybridPoint(math.inf, -1, -1, -1, -1, beta)

    for u in range(0, beta - 1):
        for q in range(0, h):
            for f in range(h - q):
                if n - f - (h - q)*u <= 0:
                    continue

                pr1 = 1.0 - (u + 1)/beta
                pr2 = 1.0 - u/beta
                if pr1 <= 0 or pr2 <= 0:
                    continue

                log_pr = (
                    f*math.log2(pr1)
                    + (h - q - f)*math.log2(pr2)
                )

                l = (n - k)//beta
                n0 = k - (u + 1)*f - (h - f - q)*u

                G1 = (
                    (n - k - l*(beta - u - 1))
                    * (n - k)
                    * ((n - k - l*(beta - u - 1)) + n0)
                )
                G1 = max(G1, 1)

                if n0 <= 0:
                    total = -log_pr + math.log2(G1)
                else:
                    m0 = (
                        (h - f - q)*(beta - u)*(beta - u - 1)/2
                        + f*(beta - u - 2)*(beta - u - 1)/2
                    )

                    w = beta*q
                    v0 = n0 - w
                    if v0 < 0:
                        continue

                    remaining = (
                        v0 + 2*q + q*v0 + q*(q - 1)//2
                    )

                    if (
                        m0 - v0*(v0 + 1)//2
                        < 2.5*remaining
                    ):
                        continue

                    G2 = max(
                        1,
                        (n0*(n0 + 1)//2 + n0) ** gauss_constant
                    )

                    G3 = (2.5*remaining) ** gauss_constant
                    G3 += (
                        2.5*remaining
                        * (v0 + 2*w + w*v0 + w*(w - 1)//2)
                    )

                    try_comp = math.log2(beta)*q

                    log_sum = _log2sum([
                        math.log2(G1),
                        math.log2(G2),
                        math.log2(G3) + try_comp,
                    ])
                    total = -log_pr + log_sum

                if total < best.cost:
                    best = HybridPoint(total, u, q, f, n0, beta)

    return best


def run_working_instance():
    p = 5
    ell = 64
    r = 528
    m = 192

    n = m*ell
    k = n-r
    h = m

    print("Standard large-field RSD benchmark mapping")
    print("="*72)
    print(f"hash field p = {p}")
    print(f"n = m*ell   = {n}")
    print(f"k = n-r     = {k}")
    print(f"h = m       = {h}")
    print(f"beta=n/h    = {n//h}")
    print()

    agb = agb2_large_field_benchmark(n, k, h)
    best_agb = agb[0]

    print("AGB 2.0 large-field author-model benchmark")
    print("-"*72)
    print(f"log2 work  = {best_agb.cost:.6f}")
    print(f"f          = {best_agb.f}")
    print(f"mu         = {best_agb.mu}")
    print(f"degree     = {best_agb.degree}")
    print(f"second f   = {best_agb.second_f}")
    print(f"second mu  = {best_agb.second_mu}")
    print()

    hyb = hybrid_large_field_benchmark(n, k, h)

    print("Hybrid large-field author-model benchmark")
    print("-"*72)
    print(f"log2 work  = {hyb.cost:.6f}")
    print(f"u          = {hyb.u}")
    print(f"q          = {hyb.q}")
    print(f"f          = {hyb.f}")
    print(f"n0         = {hyb.n0}")
    print(f"beta       = {hyb.beta}")
    print()

    known_enum = 493.965
    print("Comparison with our current coefficient-aware Enum result")
    print("-"*72)
    print(f"Enum       = {known_enum:.3f}")
    print(f"AGB 2.0    = {best_agb.cost:.3f}")
    print(f"Hybrid RSD = {hyb.cost:.3f}")
    print(f"minimum    = {min(known_enum, best_agb.cost, hyb.cost):.3f}")
    print("="*72)

    return best_agb, hyb


if __name__ == "__main__":
    run_working_instance()
