
import math
from dataclasses import dataclass
from typing import List, Optional, Tuple

import numpy as np


NEG_INF = -np.inf


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


def logadd2_scalar(a: float, b: float) -> float:
    if not math.isfinite(a):
        return b
    if not math.isfinite(b):
        return a
    m = max(a, b)
    return m + math.log2(2.0 ** (a - m) + 2.0 ** (b - m))


def log2_one_minus_exp_minus_from_log2mu(log2mu: float) -> float:


    if log2mu < -40.0:
        return log2mu
    if log2mu > 6.0:
        return 0.0
    mu = 2.0 ** log2mu
    return math.log2(-math.expm1(-mu))


def log2_rank_probability(p: int, r: int, lam: int) -> float:
    return sum(
        math.log2(1.0 - p ** (-j))
        for j in range(lam + 1, r + 1)
    )


def balanced_values(total: int, count: int, lo: int, hi: int):


    if count == 0:
        return [] if total == 0 else None
    if total < count * lo or total > count * hi:
        return None

    shifted = total - count * lo
    span = hi - lo
    f, b = divmod(shifted, count)

    if f > span or (b and f + 1 > span):
        return None

    vals = [lo + f + 1] * b + [lo + f] * (count - b)
    return vals


def make_fixed_profile(
    ell: int,
    r: int,
    m: int,
    lam: int,
    u: int,
    R_U: int,
):


    pivot_total = r - lam
    v = m - u
    R_V = pivot_total - R_U

    tU = balanced_values(R_U, u, 0, ell - 1)
    tV = balanced_values(R_V, v, 1, ell)

    if tU is None or tV is None:
        return None


    active = [(True, t) for t in tU]
    zero = [(False, t) for t in tV]

    blocks = []
    ia = iz = 0
    while ia < len(active) or iz < len(zero):
        if ia < len(active):
            blocks.append(active[ia])
            ia += 1
        if iz < len(zero):
            blocks.append(zero[iz])
            iz += 1

    H1 = blocks[0::2]
    H2 = blocks[1::2]

    return H1, H2


def half_capacity_logpoly(p: int, ell: int, half):


    n = len(half)
    coeff = np.full(n + 1, -np.inf, dtype=float)
    coeff[0] = 0.0
    deg = 0

    for is_active, t in half:
        q = ell - t
        c = q * (p - 1)
        lc = math.log2(c) if c > 0 else -math.inf

        new = np.full(n + 1, -np.inf, dtype=float)
        new[:deg + 1] = coeff[:deg + 1]

        if math.isfinite(lc):
            shifted = coeff[:deg + 1] + lc
            new[1:deg + 2] = logadd2_vec(
                new[1:deg + 2],
                shifted,
            )

        coeff = new
        deg += 1

    return coeff


def half_representation_logmatrix(p: int, ell: int, half):


    n = len(half)
    M = np.full((n + 1, n + 1), -np.inf, dtype=float)
    M[0, 0] = 0.0
    deg = 0

    for is_active, t in half:
        q = ell - t
        new = np.full_like(M, -np.inf)

        if is_active:

            new[1:deg + 2, :deg + 1] = logadd2_vec(
                new[1:deg + 2, :deg + 1],
                M[:deg + 1, :deg + 1],
            )


            new[:deg + 1, 1:deg + 2] = logadd2_vec(
                new[:deg + 1, 1:deg + 2],
                M[:deg + 1, :deg + 1],
            )


            if p - 2 > 0:
                lc = math.log2(p - 2)
                new[1:deg + 2, 1:deg + 2] = logadd2_vec(
                    new[1:deg + 2, 1:deg + 2],
                    M[:deg + 1, :deg + 1] + lc,
                )

        else:

            new[:deg + 1, :deg + 1] = logadd2_vec(
                new[:deg + 1, :deg + 1],
                M[:deg + 1, :deg + 1],
            )


            c = q * (p - 1)
            if c > 0:
                lc = math.log2(c)
                new[1:deg + 2, 1:deg + 2] = logadd2_vec(
                    new[1:deg + 2, 1:deg + 2],
                    M[:deg + 1, :deg + 1] + lc,
                )

        M = new
        deg += 1

    return M


def fixed_profile_log2_mean_preimages(
    p: int,
    ell: int,
    r: int,
    half1,
    half2,
):


    log_count = 0.0

    for half in (half1, half2):
        for is_active, t in half:
            q = ell - t
            if is_active:
                choices = q * (p - 1)
            else:
                choices = t * (p - 1)

            if choices <= 0:
                return -math.inf

            log_count += math.log2(choices)

    return log_count - r * math.log2(p)


@dataclass
class RepResult:
    p: int
    ell: int
    r: int
    m: int
    lam: int
    u: int
    R_U: int

    a1: int
    a2: int
    tau: int

    log2_R: float
    log2_survival: float
    log2_mean_preimages_profile: float
    log2_delta: float

    log2_leaf1: float
    log2_leaf2: float
    log2_intermediate: float
    log2_final_matches: float

    rank_penalty: float
    work_exponent: float
    memory_exponent: float


def optimize_fixed_profile_rep(
    p: int,
    ell: int,
    r: int,
    m: int,
    lam: int,
    u: int,
    R_U: int,
    tau_slack: int = 4,
    top_k: int = 20,
) -> List[RepResult]:

    profile = make_fixed_profile(
        ell=ell,
        r=r,
        m=m,
        lam=lam,
        u=u,
        R_U=R_U,
    )

    if profile is None:
        return []

    H1, H2 = profile

    C1 = half_capacity_logpoly(p, ell, H1)
    C2 = half_capacity_logpoly(p, ell, H2)

    R1 = half_representation_logmatrix(p, ell, H1)
    R2 = half_representation_logmatrix(p, ell, H2)

    logmu = fixed_profile_log2_mean_preimages(
        p=p,
        ell=ell,
        r=r,
        half1=H1,
        half2=H2,
    )

    rank_log = log2_rank_probability(p, r, lam)
    rank_penalty = -rank_log

    logp = math.log2(p)
    log_la = 3.0 * math.log2(r)

    results = []


    for a1 in range(len(C1)):
        if not math.isfinite(C1[a1]) or not math.isfinite(R1[a1, a1]):
            continue

        for a2 in range(len(C2)):
            if not math.isfinite(C2[a2]) or not math.isfinite(R2[a2, a2]):
                continue

            logR = R1[a1, a1] + R2[a2, a2]


            tau_center = int(round(logR / logp))
            tau_lo = max(0, tau_center - tau_slack)
            tau_hi = min(lam, tau_center + tau_slack)


            tau_values = sorted(set(
                list(range(tau_lo, tau_hi + 1))
                + [0, lam]
            ))

            leaf1 = C1[a1]
            leaf2 = C2[a2]

            for tau in tau_values:


                logL = leaf1 + leaf2 - tau * logp

                if logL < -20:
                    continue


                logmean_rep_survive = logR - tau * logp
                logsurv = log2_one_minus_exp_minus_from_log2mu(
                    logmean_rep_survive
                )

                logdelta = logmu + logsurv
                logpsucc = log2_one_minus_exp_minus_from_log2mu(
                    logdelta
                )


                log_final_matches = (
                    2.0 * logL
                    - (lam - tau) * logp
                )


                log_leaf_cost = max(leaf1, leaf2) + 2.0
                log_mid_cost = logL + 1.0

                if r > lam:
                    log_final_cost = (
                        log_final_matches
                        + math.log2(r - lam)
                    )
                else:
                    log_final_cost = log_final_matches

                Mx = max(
                    log_la,
                    log_leaf_cost,
                    log_mid_cost,
                    log_final_cost,
                )

                terms = [
                    2.0 ** (log_la - Mx),
                    2.0 ** (log_leaf_cost - Mx),
                    2.0 ** (log_mid_cost - Mx),
                    2.0 ** (log_final_cost - Mx),
                ]
                log_iter_cost = Mx + math.log2(sum(terms))

                total = log_iter_cost - rank_log - logpsucc

                memory = max(leaf1, leaf2, logL)

                results.append(
                    RepResult(
                        p=p,
                        ell=ell,
                        r=r,
                        m=m,
                        lam=lam,
                        u=u,
                        R_U=R_U,
                        a1=a1,
                        a2=a2,
                        tau=tau,
                        log2_R=logR,
                        log2_survival=logsurv,
                        log2_mean_preimages_profile=logmu,
                        log2_delta=logdelta,
                        log2_leaf1=leaf1,
                        log2_leaf2=leaf2,
                        log2_intermediate=logL,
                        log2_final_matches=log_final_matches,
                        rank_penalty=rank_penalty,
                        work_exponent=total,
                        memory_exponent=memory,
                    )
                )

    results.sort(
        key=lambda z: (
            z.work_exponent,
            z.memory_exponent,
            z.tau,
        )
    )

    return results[:top_k]


def print_results(results: List[RepResult], title: Optional[str] = None):
    if title:
        print("\n" + title)

    print(
        f"{'work':>10} {'a1':>4} {'a2':>4} {'tau':>5} "
        f"{'log2R':>10} {'surv':>9} {'mu':>9} "
        f"{'delta':>9} {'L':>10} {'mem':>10}"
    )

    for z in results:
        print(
            f"{z.work_exponent:10.3f} "
            f"{z.a1:4d} "
            f"{z.a2:4d} "
            f"{z.tau:5d} "
            f"{z.log2_R:10.3f} "
            f"{z.log2_survival:9.3f} "
            f"{z.log2_mean_preimages_profile:9.3f} "
            f"{z.log2_delta:9.3f} "
            f"{z.log2_intermediate:10.3f} "
            f"{z.memory_exponent:10.3f}"
        )


if __name__ == "__main__":

    R = optimize_fixed_profile_rep(
        p=5,
        ell=64,
        r=528,
        m=192,
        lam=208,
        u=120,
        R_U=0,
        tau_slack=4,
        top_k=20,
    )

    print_results(
        R,
        "p-ary depth-2 representation attack -- fixed working profile"
    )
