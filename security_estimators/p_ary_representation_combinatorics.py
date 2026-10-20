
import math
import itertools
from dataclasses import dataclass
from typing import List, Tuple, Optional


NEG_INF = float("-inf")


def log2_binom(n: int, k: int) -> float:
    if k < 0 or k > n:
        return NEG_INF
    return (
        math.lgamma(n + 1)
        - math.lgamma(k + 1)
        - math.lgamma(n - k + 1)
    ) / math.log(2.0)


def log2_multinomial3(n: int, a: int, b: int, c: int) -> float:
    if min(a, b, c) < 0 or a + b + c != n:
        return NEG_INF
    return (
        math.lgamma(n + 1)
        - math.lgamma(a + 1)
        - math.lgamma(b + 1)
        - math.lgamma(c + 1)
    ) / math.log(2.0)


def log2_add(x: float, y: float) -> float:
    if x == NEG_INF:
        return y
    if y == NEG_INF:
        return x
    m = max(x, y)
    return m + math.log2(2.0 ** (x - m) + 2.0 ** (y - m))


def representation_count_exact(
    p: int,
    ell: int,
    B: int,
    u: int,
    a: int,
    b: int,
) -> int:


    if p < 2 or ell <= 0:
        raise ValueError("Require p>=2 and ell>0.")
    if not (0 <= u <= B and 0 <= a <= B and 0 <= b <= B):
        return 0

    z = B - u
    Q0 = ell * (p - 1)

    total = 0

    for e in range(z + 1):
        c = a + b - u - 2 * e
        l = a - c - e
        r = b - c - e

        if min(c, l, r) < 0:
            continue
        if l + r + c != u:
            continue
        if c > u:
            continue


        multinomial = math.factorial(u) // (
            math.factorial(l) * math.factorial(r) * math.factorial(c)
        )

        if p == 2 and c > 0:
            continue

        coeff_overlap = (p - 2) ** c
        zero_cancel = math.comb(z, e) * (Q0 ** e)

        total += multinomial * coeff_overlap * zero_cancel

    return total


def log2_representation_count(
    p: int,
    ell: int,
    B: int,
    u: int,
    a: int,
    b: int,
) -> float:


    if p < 2 or ell <= 0:
        raise ValueError("Require p>=2 and ell>0.")
    if not (0 <= u <= B and 0 <= a <= B and 0 <= b <= B):
        return NEG_INF

    z = B - u
    Q0 = ell * (p - 1)

    ans = NEG_INF

    for e in range(z + 1):
        c = a + b - u - 2 * e
        l = a - c - e
        r = b - c - e

        if min(c, l, r) < 0 or l + r + c != u:
            continue

        if p == 2 and c > 0:
            continue

        term = log2_multinomial3(u, l, r, c)

        if c:
            if p - 2 == 0:
                continue
            term += c * math.log2(p - 2)

        if e:
            term += log2_binom(z, e)
            term += e * math.log2(Q0)

        ans = log2_add(ans, term)

    return ans


def log2_component_capacity(p: int, ell: int, B: int, weight: int) -> float:


    if weight < 0 or weight > B:
        return NEG_INF

    Q = ell * (p - 1)

    return log2_binom(B, weight) + weight * math.log2(Q)


@dataclass
class RepresentationProfile:
    p: int
    ell: int
    B: int
    u: int
    a: int
    b: int
    log2_representations: float
    log2_left_capacity: float
    log2_right_capacity: float
    log2_pair_space: float
    log2_representation_density: float


def profile(
    p: int,
    ell: int,
    B: int,
    u: int,
    a: int,
    b: int,
) -> RepresentationProfile:
    logR = log2_representation_count(p, ell, B, u, a, b)
    logCL = log2_component_capacity(p, ell, B, a)
    logCR = log2_component_capacity(p, ell, B, b)

    return RepresentationProfile(
        p=p,
        ell=ell,
        B=B,
        u=u,
        a=a,
        b=b,
        log2_representations=logR,
        log2_left_capacity=logCL,
        log2_right_capacity=logCR,
        log2_pair_space=logCL + logCR,
        log2_representation_density=logR - logCL - logCR,
    )


def best_symmetric_profiles(
    p: int,
    ell: int,
    B: int,
    u: int,
    top_k: int = 10,
) -> List[RepresentationProfile]:


    out = []

    for w in range(B + 1):
        P = profile(p, ell, B, u, w, w)
        if P.log2_representations != NEG_INF:
            out.append(P)

    out.sort(
        key=lambda P: (
            -P.log2_representations,
            P.log2_pair_space,
        )
    )
    return out[:top_k]


def gamma_elements(p: int, ell: int):


    out = [None]
    for j in range(ell):
        for c in range(1, p):
            out.append((j, c))
    return out


def gamma_add(x, y, p: int):


    if x is None:
        return y
    if y is None:
        return x

    jx, cx = x
    jy, cy = y

    if jx != jy:
        return "invalid"

    c = (cx + cy) % p
    if c == 0:
        return None

    return (jx, c)


def block_weight(vec) -> int:
    return sum(v is not None for v in vec)


def brute_force_count(
    p: int,
    ell: int,
    B: int,
    u: int,
    a: int,
    b: int,
) -> int:


    G = gamma_elements(p, ell)
    target = [(0, 1)] * u + [None] * (B - u)

    all_vecs = list(itertools.product(G, repeat=B))
    left = [x for x in all_vecs if block_weight(x) == a]
    right = [y for y in all_vecs if block_weight(y) == b]

    count = 0

    for x in left:
        for y in right:
            s = tuple(gamma_add(xx, yy, p) for xx, yy in zip(x, y))
            if "invalid" in s:
                continue
            if list(s) == target:
                count += 1

    return count


def validate_small():
    tests = [

        (2, 2, 2, 1, 1, 0),
        (2, 2, 2, 0, 1, 1),
        (3, 2, 2, 1, 1, 1),
        (3, 2, 2, 1, 2, 1),
        (5, 1, 2, 1, 1, 1),
    ]

    print("Exact formula vs exhaustive enumeration")
    print("-" * 72)

    ok = True
    for t in tests:
        exact = representation_count_exact(*t)
        brute = brute_force_count(*t)
        good = exact == brute
        ok &= good

        print(
            f"{t}: formula={exact:6d}, brute={brute:6d}, "
            f"match={good}"
        )

    print("-" * 72)
    print("All validation tests passed:", ok)
    return ok


def print_profiles(profiles: List[RepresentationProfile], title: Optional[str] = None):
    if title:
        print("\n" + title)

    print(
        f"{'a=b':>6} {'log2R':>12} {'log2CL':>12} "
        f"{'log2CR':>12} {'log2 density':>14}"
    )

    for P in profiles:
        print(
            f"{P.a:6d} "
            f"{P.log2_representations:12.3f} "
            f"{P.log2_left_capacity:12.3f} "
            f"{P.log2_right_capacity:12.3f} "
            f"{P.log2_representation_density:14.3f}"
        )


if __name__ == "__main__":
    validate_small()


    P = best_symmetric_profiles(
        p=5,
        ell=64,
        B=120,
        u=120,
        top_k=12,
    )

    print_profiles(
        P,
        title=(
            "p=5, ell=64, B=120, u=120 -- "
            "exact symmetric representation profiles"
        )
    )
