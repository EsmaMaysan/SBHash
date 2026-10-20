
import csv
import json
import math
import time
import importlib.util
from pathlib import Path


P = 5
ELL = 64
R = 528
M = 192
TARGET_BITS = 128.0


LAMBDA_STEP = 12
U_STEP = 8


RU_SAMPLES = 5


TAU_SLACK = 4


INNER_TOP_K = 1


BASE_DIR = Path(__file__).resolve().parent if "__file__" in globals() else Path.cwd()
STATE_FILE = BASE_DIR / "rep_global_state.json"
RESULTS_FILE = BASE_DIR / "rep_global_results.csv"
TOP_FILE = BASE_DIR / "rep_global_top.csv"


def _load_fixed_estimator():
    path = BASE_DIR / "p_ary_regular_isd_rep_fixed_profile.py"
    if not path.exists():
        raise FileNotFoundError(
            "Place p_ary_regular_isd_rep_fixed_profile.py in the same "
            "Jupyter directory as this script."
        )

    spec = importlib.util.spec_from_file_location("repfixed", str(path))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


REPFIXED = _load_fixed_estimator()


def feasible_ru_interval(lam, u):


    pivot_total = R - lam
    v = M - u

    lo = max(
        0,
        pivot_total - v * ELL,
    )

    hi = min(
        u * (ELL - 1),
        pivot_total - v,
    )

    if lo > hi:
        return None

    return int(lo), int(hi)


def sampled_ru_values(lam, u, samples=RU_SAMPLES):
    interval = feasible_ru_interval(lam, u)
    if interval is None:
        return []

    lo, hi = interval

    if lo == hi:
        return [lo]

    vals = {lo, hi}


    pivot_total = R - lam
    prop = round(u * pivot_total / M)
    vals.add(max(lo, min(hi, prop)))


    if lo <= 0 <= hi:
        vals.add(0)


    if samples >= 2:
        for j in range(samples):
            x = lo + round((hi - lo) * j / (samples - 1))
            vals.add(int(x))

    return sorted(vals)


def build_coarse_grid():
    jobs = []

    lambdas = list(range(1, R, LAMBDA_STEP))
    if (R - 1) not in lambdas:
        lambdas.append(R - 1)

    us = list(range(2, M + 1, U_STEP))
    if M not in us:
        us.append(M)

    for lam in lambdas:
        for u in us:
            for RU in sampled_ru_values(lam, u):
                jobs.append({
                    "stage": "coarse",
                    "lam": int(lam),
                    "u": int(u),
                    "R_U": int(RU),
                })


    jobs.append({
        "stage": "anchor",
        "lam": 208,
        "u": 120,
        "R_U": 0,
    })


    unique = {}
    for j in jobs:
        key = (j["lam"], j["u"], j["R_U"])
        unique[key] = j

    return list(unique.values())


def load_state():
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))

    jobs = build_coarse_grid()

    state = {
        "version": 1,
        "p": P,
        "ell": ELL,
        "r": R,
        "m": M,
        "jobs": jobs,
        "next_index": 0,
        "completed": 0,
        "failures": 0,
    }

    save_state(state)
    return state


def save_state(state):
    STATE_FILE.write_text(
        json.dumps(state, indent=2),
        encoding="utf-8",
    )


CSV_FIELDS = [
    "stage",
    "lam",
    "u",
    "R_U",
    "work",
    "memory",
    "a1",
    "a2",
    "tau",
    "log2_R",
    "log2_survival",
    "log2_mean_preimages_profile",
    "log2_delta",
    "log2_leaf1",
    "log2_leaf2",
    "log2_intermediate",
    "log2_final_matches",
    "rank_penalty",
]


def append_result(job, z):
    exists = RESULTS_FILE.exists()

    row = {
        "stage": job["stage"],
        "lam": z.lam,
        "u": z.u,
        "R_U": z.R_U,
        "work": float(z.work_exponent),
        "memory": float(z.memory_exponent),
        "a1": z.a1,
        "a2": z.a2,
        "tau": z.tau,
        "log2_R": float(z.log2_R),
        "log2_survival": float(z.log2_survival),
        "log2_mean_preimages_profile": float(z.log2_mean_preimages_profile),
        "log2_delta": float(z.log2_delta),
        "log2_leaf1": float(z.log2_leaf1),
        "log2_leaf2": float(z.log2_leaf2),
        "log2_intermediate": float(z.log2_intermediate),
        "log2_final_matches": float(z.log2_final_matches),
        "rank_penalty": float(z.rank_penalty),
    }

    with RESULTS_FILE.open("a", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=CSV_FIELDS)
        if not exists:
            writer.writeheader()
        writer.writerow(row)


def read_results():
    if not RESULTS_FILE.exists():
        return []

    rows = []
    with RESULTS_FILE.open("r", newline="", encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            out = dict(row)
            for k in CSV_FIELDS:
                if k in ("stage",):
                    continue
                if k in ("lam", "u", "R_U", "a1", "a2", "tau"):
                    out[k] = int(float(out[k]))
                else:
                    out[k] = float(out[k])
            rows.append(out)

    return rows


def write_top(k=30):
    rows = read_results()
    rows.sort(key=lambda x: (x["work"], x["memory"]))

    with TOP_FILE.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=CSV_FIELDS)
        writer.writeheader()
        for row in rows[:k]:
            writer.writerow(row)

    return rows[:k]


def afficher_top(k=15):
    top = write_top(k)

    if not top:
        print("Aucun résultat pour le moment.")
        return

    print(
        f"{'work':>10} {'lam':>5} {'u':>5} {'RU':>6} "
        f"{'a1':>4} {'a2':>4} {'tau':>5} "
        f"{'log2R':>10} {'mem':>10}"
    )

    for z in top:
        print(
            f"{z['work']:10.3f} "
            f"{z['lam']:5d} "
            f"{z['u']:5d} "
            f"{z['R_U']:6d} "
            f"{z['a1']:4d} "
            f"{z['a2']:4d} "
            f"{z['tau']:5d} "
            f"{z['log2_R']:10.3f} "
            f"{z['memory']:10.3f}"
        )


def progression():
    state = load_state()
    n = len(state["jobs"])
    done = state["next_index"]

    pct = 100.0 * done / n if n else 100.0

    print(f"Profils calculés : {done:,}/{n:,}")
    print(f"Progression      : {pct:.2f}%")
    print(f"Échecs           : {state['failures']:,}")

    rows = read_results()
    if rows:
        best = min(rows, key=lambda x: x["work"])
        print(
            "Meilleur actuel  : "
            f"{best['work']:.3f} bits "
            f"(lambda={best['lam']}, u={best['u']}, "
            f"R_U={best['R_U']}, a1={best['a1']}, "
            f"a2={best['a2']}, tau={best['tau']})"
        )


def EXECUTER_LOT(max_profils=16, max_secondes=30):


    state = load_state()
    jobs = state["jobs"]

    start = time.time()
    processed = 0

    while state["next_index"] < len(jobs):
        if processed >= max_profils:
            break
        if time.time() - start >= max_secondes:
            break

        idx = state["next_index"]
        job = jobs[idx]

        try:
            out = REPFIXED.optimize_fixed_profile_rep(
                p=P,
                ell=ELL,
                r=R,
                m=M,
                lam=job["lam"],
                u=job["u"],
                R_U=job["R_U"],
                tau_slack=TAU_SLACK,
                top_k=INNER_TOP_K,
            )

            if out:
                append_result(job, out[0])

        except Exception as exc:
            state["failures"] += 1
            print(
                f"\nÉchec profil #{idx}: "
                f"lambda={job['lam']}, u={job['u']}, "
                f"R_U={job['R_U']} -> {exc}"
            )

        state["next_index"] += 1
        state["completed"] += 1
        processed += 1
        save_state(state)

    write_top()

    print()
    progression()


def ajouter_raffinement(
    top_n=12,
    lambda_radius=12,
    u_radius=8,
    ru_radius=16,
    lambda_step=2,
    u_step=2,
    ru_step=4,
):


    state = load_state()
    rows = read_results()

    if not rows:
        print("Aucun résultat à raffiner.")
        return

    rows.sort(key=lambda x: (x["work"], x["memory"]))
    seeds = rows[:top_n]

    existing = {
        (j["lam"], j["u"], j["R_U"])
        for j in state["jobs"]
    }

    new_jobs = []

    for s in seeds:
        for lam in range(
            max(1, s["lam"] - lambda_radius),
            min(R - 1, s["lam"] + lambda_radius) + 1,
            lambda_step,
        ):
            for u in range(
                max(2, s["u"] - u_radius),
                min(M, s["u"] + u_radius) + 1,
                u_step,
            ):
                interval = feasible_ru_interval(lam, u)
                if interval is None:
                    continue

                lo, hi = interval

                rlo = max(lo, s["R_U"] - ru_radius)
                rhi = min(hi, s["R_U"] + ru_radius)

                for RU in range(rlo, rhi + 1, ru_step):
                    key = (lam, u, RU)
                    if key in existing:
                        continue

                    existing.add(key)
                    new_jobs.append({
                        "stage": "refine",
                        "lam": int(lam),
                        "u": int(u),
                        "R_U": int(RU),
                    })

    state["jobs"].extend(new_jobs)
    save_state(state)

    print(f"{len(new_jobs):,} nouveaux profils de raffinement ajoutés.")
    progression()


def reinitialiser():


    for path in (STATE_FILE, RESULTS_FILE, TOP_FILE):
        if path.exists():
            path.unlink()

    state = load_state()
    print("Recherche réinitialisée.")
    progression()


if __name__ == "__main__":
    print("Global p-ary Rep search")
    print("------------------------")
    progression()
    print()
    print("In Jupyter, run repeatedly:")
    print("    EXECUTER_LOT(max_profils=16, max_secondes=30)")
    print()
    print("After reaching 100%:")
    print("    afficher_top()")
    print("    ajouter_raffinement()")
    print("    EXECUTER_LOT(max_profils=16, max_secondes=30)")
