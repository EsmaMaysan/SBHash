
import math
import heapq
from dataclasses import dataclass
from typing import List, Tuple, Optional

NEG_INF = float("-inf")


def logadd2(a: float, b: float) -> float:

    if a == NEG_INF:
        return b
    if b == NEG_INF:
        return a
    m = max(a, b)
    return m + math.log2(2.0 ** (a - m) + 2.0 ** (b - m))


def logsum2(values) -> float:

    values = [v for v in values if v != NEG_INF]
    if not values:
        return NEG_INF
    m = max(values)
    return m + math.log2(sum(2.0 ** (v - m) for v in values))


def D_local(p: int, t: int, binary_fsb: bool = False) -> int:


    if binary_fsb:
        return 1 + t * (t - 1) // 2

    return (
        1
        + t * (p - 1)
        + (t * (t - 1) // 2) * (p - 1) ** 2
    )


def E_local(p: int, t: int, binary_fsb: bool = False) -> int:


    if binary_fsb:
        return t

    return 1 + t * (p - 1)


def log2_invertibility_probability(p: int, r: int) -> float:


    return sum(math.log2(1.0 - p ** (-j)) for j in range(1, r + 1))


def balanced_layout(
    ell: int,
    r: int,
    w0: int,
    lam: int,
) -> Optional[Tuple[List[Tuple[int, int, int]],
                    List[Tuple[int, int, int]]]]:


    if w0 % 2 != 0:
        return None
    if not (0 <= lam < r):
        return None

    h = w0 // 2
    q_total = r - lam
    q_base, q_rem = divmod(q_total, w0)


    q_rem_left = (q_rem + 1) // 2
    q_rem_right = q_rem // 2

    q_left = [q_base + 1] * q_rem_left + [q_base] * (h - q_rem_left)
    q_right = [q_base + 1] * q_rem_right + [q_base] * (h - q_rem_right)

    lam_left = (lam + 1) // 2
    lam_right = lam // 2

    def allocate_S(q_values, s_total):


        s = [0] * len(q_values)
        heap = [(q_values[i], i) for i in range(len(q_values))]
        heapq.heapify(heap)

        for _ in range(s_total):
            current, i = heapq.heappop(heap)


            if current >= ell - 1:
                return None

            s[i] += 1
            heapq.heappush(heap, (current + 1, i))

        return s

    s_left = allocate_S(q_left, lam_left)
    s_right = allocate_S(q_right, lam_right)

    if s_left is None or s_right is None:
        return None

    left = [(q, s, ell - q - s) for q, s in zip(q_left, s_left)]
    right = [(q, s, ell - q - s) for q, s in zip(q_right, s_right)]

    if min(u for _, _, u in left + right) <= 0:
        return None

    return left, right


def elementary_log_arrays(
    blocks: List[Tuple[int, int, int]],
    p: int,
    binary_fsb: bool = False,
):


    h = len(blocks)

    logC = [NEG_INF] * (h + 1)
    logW = [NEG_INF] * (h + 1)
    logC[0] = 0.0
    logW[0] = 0.0

    for idx, (q, s, u) in enumerate(blocks):
        coefficient_choices = 1 if binary_fsb else (p - 1)
        c = coefficient_choices * u

        if c <= 0:
            continue

        logc = math.log2(c)
        D = D_local(p, q, binary_fsb)
        E = E_local(p, q, binary_fsb)

        logw = NEG_INF
        if E > 0:
            logw = logc + math.log2(E) - math.log2(D)

        for k in range(idx + 1, 0, -1):
            logC[k] = logadd2(logC[k], logC[k - 1] + logc)

            if logw != NEG_INF and logW[k - 1] != NEG_INF:
                logW[k] = logadd2(logW[k], logW[k - 1] + logw)

    return logC, logW


def log2_success_probability(log2_delta: float) -> float:


    if log2_delta < -40.0:

        return log2_delta

    if log2_delta > 6.0:
        return 0.0

    delta = 2.0 ** log2_delta
    prob = -math.expm1(-delta)
    return math.log2(prob)


@dataclass
class ISDResult:
    log2_work: float
    w0: int
    x: int
    lam: int
    f: int
    log2_N: float
    log2_delta: float
    log2_capacity: float
    log2_memory_bits: float
    log2_pinv: float


def optimize_log2_N(
    p: int,
    r: int,
    lam: int,
    x: int,
    log2_capacity: float,
    log2_delta_constant: float,
    log2_pinv: float,
):


    z_sat = -0.5 * log2_delta_constant
    z0 = min(log2_capacity, max(0.0, z_sat))

    candidates = {0.0, log2_capacity, z0}

    for d in (
        -4.0, -3.0, -2.0, -1.5, -1.0, -0.5,
         0.0,  0.5,  1.0,  1.5,  2.0,  3.0, 4.0
    ):
        z = z0 + d
        if 0.0 <= z <= log2_capacity:
            candidates.add(z)

    best = None

    for z in candidates:
        log2_delta = 2.0 * z + log2_delta_constant
        log2_psucc = log2_success_probability(log2_delta)


        log2_la = 3.0 * math.log2(r)

        terms = [log2_la]


        if lam > 0:
            log2_list = (
                log2_pinv
                + 1.0
                + z
                + math.log2(lam)
            )
            terms.append(log2_list)

        if r > lam:
            log2_checks = (
                log2_pinv
                + 2.0 * z
                - lam * math.log2(p)
                + math.log2(2.0 * x * (r - lam))
            )
            terms.append(log2_checks)

        log2_cost_per_random_selection = logsum2(terms)


        log2_total_work = (
            log2_cost_per_random_selection
            - log2_pinv
            - log2_psucc
        )

        if best is None or log2_total_work < best[0]:
            best = (log2_total_work, z, log2_delta)

    return best


def optimize_p_ary_regular_isd(
    p: int,
    ell: int,
    r: int,
    m: int,
    binary_fsb: bool = False,
    top_k: int = 10,
    verbose: bool = True,
):


    if not binary_fsb and p <= 2:
        raise ValueError(
            "For p=2 use binary_fsb=True; the local difference set "
            "does not contain weight-one vectors."
        )

    log2_pinv = log2_invertibility_probability(p, r)

    w0_min = math.ceil(r / ell)
    if w0_min % 2:
        w0_min += 1

    w0_max = min(m, r)
    results = []

    tested = 0

    for w0 in range(w0_min, w0_max + 1, 2):
        half = w0 // 2


        f_max = min(ell - 1, r // w0)

        for f in range(1, f_max + 1):
            lam = r - f * w0

            if not (0 <= lam < r):
                continue

            layout = balanced_layout(ell, r, w0, lam)
            if layout is None:
                continue

            left, right = layout

            logC_L, logW_L = elementary_log_arrays(
                left, p, binary_fsb
            )
            logC_R, logW_R = elementary_log_arrays(
                right, p, binary_fsb
            )

            log2_D_all = sum(
                math.log2(D_local(p, q, binary_fsb))
                for half_blocks in layout
                for q, s, u in half_blocks
            )

            projective_correction = (
                0.0 if binary_fsb else math.log2(p - 1)
            )

            for x in range(1, half + 1):
                if (
                    logC_L[x] == NEG_INF
                    or logC_R[x] == NEG_INF
                    or logW_L[x] == NEG_INF
                    or logW_R[x] == NEG_INF
                ):
                    continue

                tested += 1

                log2_capacity = min(logC_L[x], logC_R[x])


                log2_completion_factor = (
                    log2_D_all
                    + (logW_L[x] - logC_L[x])
                    + (logW_R[x] - logC_R[x])
                )


                log2_delta_constant = (
                    log2_completion_factor
                    - r * math.log2(p)
                    - projective_correction
                )

                opt = optimize_log2_N(
                    p=p,
                    r=r,
                    lam=lam,
                    x=x,
                    log2_capacity=log2_capacity,
                    log2_delta_constant=log2_delta_constant,
                    log2_pinv=log2_pinv,
                )

                log2_work, log2_N, log2_delta = opt


                if lam > 0:
                    bits_per_field_element = math.ceil(math.log2(p))
                    log2_memory_bits = (
                        1.0
                        + log2_N
                        + math.log2(lam)
                        + math.log2(bits_per_field_element)
                    )
                else:
                    log2_memory_bits = log2_N + 1.0

                results.append(
                    ISDResult(
                        log2_work=log2_work,
                        w0=w0,
                        x=x,
                        lam=lam,
                        f=f,
                        log2_N=log2_N,
                        log2_delta=log2_delta,
                        log2_capacity=log2_capacity,
                        log2_memory_bits=log2_memory_bits,
                        log2_pinv=log2_pinv,
                    )
                )

        if verbose:
            print(
                f"w0={w0:4d}/{w0_max} | "
                f"configurations testees: {tested:,}",
                end="\r"
            )

    if verbose:
        print()

    results.sort(key=lambda z: z.log2_work)
    return results[:top_k]


def print_results(results, title=None):
    if title:
        print("\n" + title)

    print(
        f"{'work':>10} {'w0':>5} {'x':>4} {'lambda':>7} "
        f"{'f':>4} {'log2N':>10} {'log2delta':>11} "
        f"{'capacity':>10} {'memory':>10}"
    )

    for z in results:
        print(
            f"{z.log2_work:10.3f} "
            f"{z.w0:5d} "
            f"{z.x:4d} "
            f"{z.lam:7d} "
            f"{z.f:4d} "
            f"{z.log2_N:10.3f} "
            f"{z.log2_delta:11.3f} "
            f"{z.log2_capacity:10.3f} "
            f"{z.log2_memory_bits:10.3f}"
        )


def validate_against_blps():


    tests = [
        ("FSB48",  2, 2**14,  192,  24),
        ("FSB160", 2, 2**14,  640,  80),
        ("FSB256", 2, 2**14, 1024, 128),
    ]

    for name, p, ell, r, m in tests:
        best = optimize_p_ary_regular_isd(
            p=p,
            ell=ell,
            r=r,
            m=m,
            binary_fsb=True,
            top_k=1,
            verbose=False,
        )[0]

        print(
            f"{name:7s}: "
            f"log2 work={best.log2_work:.3f}, "
            f"w0={best.w0}, x={best.x}, "
            f"log2 N={best.log2_N:.3f}, "
            f"lambda={best.lam}"
        )
