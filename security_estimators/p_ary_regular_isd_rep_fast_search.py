
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

BASE_DIR = Path(__file__).resolve().parent if "__file__" in globals() else Path.cwd()

STATE_FILE = BASE_DIR / "rep_fast_state.json"
RESULTS_FILE = BASE_DIR / "rep_fast_results.csv"
TOP_FILE = BASE_DIR / "rep_fast_top.csv"


def _load_fixed_estimator():
    path = BASE_DIR / "p_ary_regular_isd_rep_fixed_profile.py"
    if not path.exists():
        raise FileNotFoundError(
            "Place p_ary_regular_isd_rep_fixed_profile.py in the same folder."
        )
    spec = importlib.util.spec_from_file_location("repfixed", str(path))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


REPFIXED = _load_fixed_estimator()


def feasible_ru_interval(lam, u):
    pivot_total = R - lam
    v = M - u

    lo = max(0, pivot_total - v * ELL)
    hi = min(u * (ELL - 1), pivot_total - v)

    if lo > hi:
        return None
    return int(lo), int(hi)


def representative_ru_values(lam, u):
    interval = feasible_ru_interval(lam, u)
    if interval is None:
        return []

    lo, hi = interval
    vals = {lo, hi}


    prop = round(u * (R - lam) / M)
    vals.add(max(lo, min(hi, prop)))


    vals.add((lo + hi) // 2)


    if lo <= 0 <= hi:
        vals.add(0)

    return sorted(vals)


def interleaved_lambda_values(step=32):
    vals = list(range(1, R, step))
    if R - 1 not in vals:
        vals.append(R - 1)


    vals = sorted(set(vals))
    out = []
    left, right = 0, len(vals) - 1
    while left <= right:
        out.append(vals[left])
        left += 1
        if left <= right:
            out.append(vals[right])
            right -= 1
    return out


def interleaved_u_values(step=16):
    vals = list(range(2, M + 1, step))
    if M not in vals:
        vals.append(M)

    vals = sorted(set(vals))
    out = []
    left, right = 0, len(vals) - 1
    while left <= right:
        out.append(vals[left])
        left += 1
        if left <= right:
            out.append(vals[right])
            right -= 1
    return out


def build_stage_A():
    jobs = []

    lambdas = interleaved_lambda_values(32)
    us = interleaved_u_values(16)


    for lam in lambdas:
        for u in us:
            for RU in representative_ru_values(lam, u):
                jobs.append({
                    "stage": "A",
                    "lam": int(lam),
                    "u": int(u),
                    "R_U": int(RU),
                })


    anchors = [
        (208, 120, 0),
        (225, 108, 0),
        (1, 2, 0),
    ]
    for lam, u, RU in anchors:
        if feasible_ru_interval(lam, u) is not None:
            lo, hi = feasible_ru_interval(lam, u)
            if lo <= RU <= hi:
                jobs.append({
                    "stage": "anchor",
                    "lam": lam,
                    "u": u,
                    "R_U": RU,
                })

    unique = {}
    for j in jobs:
        unique[(j["lam"], j["u"], j["R_U"])] = j

    return list(unique.values())


CSV_FIELDS = [
    "stage", "lam", "u", "R_U",
    "work", "memory", "a1", "a2", "tau",
    "log2_R", "log2_survival",
    "log2_mean_preimages_profile", "log2_delta",
    "log2_leaf1", "log2_leaf2",
    "log2_intermediate", "log2_final_matches",
    "rank_penalty",
]


def save_state(state):
    STATE_FILE.write_text(json.dumps(state, indent=2), encoding="utf-8")


def load_state():
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))

    state = {
        "version": 1,
        "jobs": build_stage_A(),
        "next_index": 0,
        "failures": 0,
        "stage_A_refined": False,
        "stage_B_refined": False,
    }
    save_state(state)
    return state


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
        w = csv.DictWriter(fh, fieldnames=CSV_FIELDS)
        if not exists:
            w.writeheader()
        w.writerow(row)


def read_results():
    if not RESULTS_FILE.exists():
        return []

    rows = []
    with RESULTS_FILE.open("r", newline="", encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            x = dict(row)
            for k in CSV_FIELDS:
                if k == "stage":
                    continue
                if k in ("lam", "u", "R_U", "a1", "a2", "tau"):
                    x[k] = int(float(x[k]))
                else:
                    x[k] = float(x[k])
            rows.append(x)
    return rows


def write_top(k=30):
    rows = read_results()
    rows.sort(key=lambda x: (x["work"], x["memory"]))
    with TOP_FILE.open("w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=CSV_FIELDS)
        w.writeheader()
        for row in rows[:k]:
            w.writerow(row)
    return rows[:k]


def progression():
    state = load_state()
    n = len(state["jobs"])
    done = state["next_index"]
    pct = 100.0 * done / n if n else 100.0

    print(f"Profils calculés : {done:,}/{n:,}")
    print(f"Progression      : {pct:.2f}%")
    print(f"Échecs           : {state['failures']}")

    rows = read_results()
    if rows:
        best = min(rows, key=lambda x: x["work"])
        print(
            f"Meilleur actuel  : {best['work']:.3f} bits "
            f"(lambda={best['lam']}, u={best['u']}, "
            f"R_U={best['R_U']}, a1={best['a1']}, "
            f"a2={best['a2']}, tau={best['tau']})"
        )


def afficher_top(k=15):
    rows = write_top(k)
    if not rows:
        print("Aucun résultat.")
        return

    print(
        f"{'work':>10} {'lam':>5} {'u':>5} {'RU':>6} "
        f"{'a1':>4} {'a2':>4} {'tau':>5} "
        f"{'log2R':>10} {'mem':>10}"
    )
    for z in rows:
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


def EXECUTER_AUTO(max_minutes=10, max_profils=256):


    state = load_state()
    start = time.time()
    processed = 0

    while state["next_index"] < len(state["jobs"]):
        if processed >= max_profils:
            break
        if time.time() - start >= 60.0 * max_minutes:
            break

        idx = state["next_index"]
        job = state["jobs"][idx]

        try:
            out = REPFIXED.optimize_fixed_profile_rep(
                p=P,
                ell=ELL,
                r=R,
                m=M,
                lam=job["lam"],
                u=job["u"],
                R_U=job["R_U"],
                tau_slack=4,
                top_k=1,
            )
            if out:
                append_result(job, out[0])
        except Exception as exc:
            state["failures"] += 1
            print(
                f"Échec #{idx}: "
                f"lambda={job['lam']}, u={job['u']}, "
                f"R_U={job['R_U']} -> {exc}"
            )

        state["next_index"] += 1
        processed += 1
        save_state(state)

    write_top()
    progression()


def _append_refinement(
    stage_name,
    seeds,
    lambda_radius,
    lambda_step,
    u_radius,
    u_step,
    ru_radius,
    ru_step,
):
    state = load_state()
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
                        "stage": stage_name,
                        "lam": int(lam),
                        "u": int(u),
                        "R_U": int(RU),
                    })

    state["jobs"].extend(new_jobs)
    save_state(state)

    print(f"{len(new_jobs):,} nouveaux profils ajoutés pour {stage_name}.")
    progression()


def raffiner_stage_B(top_n=8):


    rows = read_results()
    if not rows:
        print("Aucun résultat à raffiner.")
        return

    rows.sort(key=lambda x: (x["work"], x["memory"]))
    seeds = rows[:top_n]

    _append_refinement(
        stage_name="B",
        seeds=seeds,
        lambda_radius=20,
        lambda_step=4,
        u_radius=12,
        u_step=4,
        ru_radius=24,
        ru_step=8,
    )


def raffiner_stage_C(top_n=4):


    rows = read_results()
    if not rows:
        print("Aucun résultat à raffiner.")
        return

    rows.sort(key=lambda x: (x["work"], x["memory"]))
    seeds = rows[:top_n]

    _append_refinement(
        stage_name="C",
        seeds=seeds,
        lambda_radius=6,
        lambda_step=1,
        u_radius=4,
        u_step=1,
        ru_radius=8,
        ru_step=2,
    )


def reinitialiser():
    for path in (STATE_FILE, RESULTS_FILE, TOP_FILE):
        if path.exists():
            path.unlink()
    load_state()
    print("Recherche rapide réinitialisée.")
    progression()


if __name__ == "__main__":
    print("Fast coarse-to-fine p-ary Rep search")
    print("--------------------------------------")
    progression()
    print()
    print("1) EXECUTER_AUTO(max_minutes=10)")
    print("2) When Stage A is complete: raffiner_stage_B()")
    print("3) EXECUTER_AUTO(max_minutes=10)")
    print("4) Then: raffiner_stage_C()")
    print("5) EXECUTER_AUTO(max_minutes=10)")
    print("6) afficher_top(20)")
