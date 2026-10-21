import argparse
import csv
import hashlib
import json
import math
import multiprocessing
import os
import platform
import sys
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

import numpy as np
import scipy
from scipy.stats import binomtest, fisher_exact


P = 5
ELL = 64
INVERSES = np.array([0, 1, 3, 2, 4], dtype=np.uint8)
PUBLIC_COLUMNS = None


def rank_fp5(matrix):
    a = np.remainder(matrix, P).astype(np.uint8, order="C", copy=True)
    if a.ndim != 2:
        raise ValueError("The input must be a two-dimensional integer matrix")
    if a.shape[0] < a.shape[1]:
        a = np.ascontiguousarray(a.T)
    rows, columns = a.shape
    rank = 0
    for column in range(columns):
        nonzero = np.flatnonzero(a[rank:, column])
        if nonzero.size == 0:
            continue
        pivot = rank + int(nonzero[0])
        if pivot != rank:
            a[[rank, pivot], column:] = a[[pivot, rank], column:]
        inverse = INVERSES[a[rank, column]]
        if inverse != 1:
            a[rank, column:] = a[rank, column:] * inverse % P
        factors = a[rank + 1:, column].copy()
        a[rank + 1:, column + 1:] = (
            a[rank + 1:, column + 1:]
            + np.uint8(20)
            - factors[:, None] * a[rank, None, column + 1:]
        ) % P
        rank += 1
        if rank == min(rows, columns):
            break
    return rank


def derive_column(seed, r, block, column, matrix_counter):
    material = (
        seed.encode("utf-8")
        + b"|MATCTR|" + matrix_counter.to_bytes(8, "big")
        + b"|BLOCK|" + block.to_bytes(4, "big")
        + b"|COL|" + column.to_bytes(4, "big")
    )
    values = []
    counter = 0
    while len(values) < r:
        buffer = hashlib.shake_256(
            b"CONSTASH_MATRIX_COL_V2" + material + counter.to_bytes(8, "big")
        ).digest(64)
        values.extend(value % P for value in buffer if value < 255)
        counter += 1
    return np.asarray(values[:r], dtype=np.uint8)


def validate_columns(columns):
    flat = columns.reshape(-1, columns.shape[-1])
    zero_count = int(np.count_nonzero(np.all(flat == 0, axis=1)))
    if zero_count:
        return zero_count, None
    leading = np.argmax(flat != 0, axis=1)
    scalars = INVERSES[flat[np.arange(len(flat)), leading]]
    normalized = flat * scalars[:, None] % P
    repetitions = len(flat) - len({row.tobytes() for row in normalized})
    return zero_count, repetitions


def generate_matrix(seed, r, m, max_attempts):
    rejected = []
    for counter in range(max_attempts):
        columns = np.empty((m, ELL, r), dtype=np.uint8)
        for block in range(m):
            for column in range(ELL):
                columns[block, column] = derive_column(
                    seed, r, block, column, counter
                )
        zero_count, repetitions = validate_columns(columns)
        if zero_count or repetitions:
            rejected.append({
                "counter": counter,
                "reason": "zero or proportional columns",
                "zero_columns": zero_count,
                "projective_repetitions": repetitions,
            })
            continue
        flat = columns.reshape(-1, r)
        prefix = r
        first_minor_rank = rank_fp5(flat[:prefix].T)
        global_rank = first_minor_rank
        while global_rank < r and prefix < len(flat):
            prefix = min(2 * prefix, len(flat))
            global_rank = rank_fp5(flat[:prefix].T)
        if global_rank < r:
            rejected.append({"counter": counter, "reason": "row rank below r"})
            continue
        columns.setflags(write=False)
        return columns, {
            "seed": seed,
            "column_domain": "CONSTASH_MATRIX_COL_V2",
            "candidate_counter": counter,
            "global_rank": global_rank,
            "first_r_column_minor_rank": first_minor_rank,
            "full_rank_witness_prefix_columns": prefix,
            "zero_columns": zero_count,
            "projective_repetitions": repetitions,
            "sha256": hashlib.sha256(columns.tobytes(order="C")).hexdigest(),
            "sha256_byte_order": "uint8 entries in block-column-coordinate order",
            "acceptance": "full row rank, no zero columns, pairwise nonproportional columns",
            "rejected_candidates": rejected,
        }
    raise RuntimeError("No acceptable public matrix was found")


def make_cases(r, m, trials, rectangular_trials):
    cases = []
    for width in sorted({64, m, 2 * m, r - 1, r, r + 1}):
        cases.append({
            "name": f"columns_{width}", "kind": "columns",
            "rows": r, "columns": width,
            "trials": trials if abs(width - r) <= 1 else rectangular_trials,
            "sampling": "uniform column subsets without replacement within each trial",
        })
    for count in sorted({1, 2, 4, r // ELL, r // ELL + 1}):
        cases.append({
            "name": f"full_blocks_{count}", "kind": "blocks",
            "rows": r, "columns": count * ELL, "blocks": count,
            "trials": m if count == 1 else rectangular_trials,
            "sampling": "all individual blocks" if count == 1 else "uniform complete-block subsets",
        })
    for count in sorted({1, 2, 4, r // ELL}):
        width = count * ELL
        cases.append({
            "name": f"square_blocks_{count}", "kind": "square_blocks",
            "rows": width, "columns": width, "blocks": count,
            "trials": trials,
            "sampling": "uniform complete-block subsets and uniform row subsets",
        })
    cases.append({
        "name": "two_columns_per_block", "kind": "two_per_block",
        "rows": r, "columns": 2 * m, "trials": rectangular_trials,
        "sampling": "two distinct uniform columns in each of the m blocks",
    })
    for case_id, case in enumerate(cases):
        case["id"] = case_id
    return cases


def initialize_worker(columns):
    global PUBLIC_COLUMNS
    PUBLIC_COLUMNS = columns


def trial_ranks(case, trial, seed):
    sequence = np.random.SeedSequence([seed, case["id"], trial])
    selection_seed, reference_seed = sequence.spawn(2)
    selection_rng = np.random.Generator(np.random.PCG64(selection_seed))
    reference_rng = np.random.Generator(np.random.PCG64(reference_seed))
    m, ell, r = PUBLIC_COLUMNS.shape
    row_indices = np.arange(r)
    if case["kind"] == "columns":
        column_indices = selection_rng.choice(
            m * ell, case["columns"], replace=False
        )
    elif case["kind"] in {"blocks", "square_blocks"}:
        if case["kind"] == "blocks" and case["blocks"] == 1:
            blocks = np.array([trial])
        else:
            blocks = selection_rng.choice(m, case["blocks"], replace=False)
        column_indices = (
            blocks[:, None] * ell + np.arange(ell)[None, :]
        ).ravel()
        if case["kind"] == "square_blocks":
            row_indices = selection_rng.choice(r, case["rows"], replace=False)
    else:
        local_columns = np.asarray([
            selection_rng.choice(ell, 2, replace=False) for _ in range(m)
        ])
        column_indices = (
            np.arange(m)[:, None] * ell + local_columns
        ).ravel()
    row_indices = np.sort(row_indices)
    column_indices = np.sort(column_indices)
    flat = PUBLIC_COLUMNS.reshape(m * ell, r)
    selected = flat[np.ix_(column_indices, row_indices)].T
    reference = reference_rng.integers(
        0, P, size=(case["rows"], case["columns"]), dtype=np.uint8
    )
    selection_bytes = (
        len(row_indices).to_bytes(4, "big")
        + row_indices.astype("<u4").tobytes()
        + len(column_indices).to_bytes(4, "big")
        + column_indices.astype("<u4").tobytes()
    )
    return {
        "case": case["name"], "trial": trial,
        "structured_rank": rank_fp5(selected),
        "reference_rank": rank_fp5(reference),
        "selection_sha256": hashlib.sha256(selection_bytes).hexdigest(),
    }


def run_batch(case, first, last, seed):
    return [trial_ranks(case, trial, seed) for trial in range(first, last)]


def deficiency_probability(rows, columns):
    logarithm = math.fsum(
        math.log1p(-P ** (-j))
        for j in range(abs(rows - columns) + 1, max(rows, columns) + 1)
    )
    return max(0.0, -math.expm1(logarithm))


def theoretical_rank_probabilities(rows, columns):
    probabilities = {}
    for rank in range(min(rows, columns) + 1):
        logarithm = -(rows - rank) * (columns - rank) * math.log(P)
        logarithm += math.fsum(
            math.log1p(-P ** (i - rows))
            + math.log1p(-P ** (i - columns))
            - math.log1p(-P ** (i - rank))
            for i in range(rank)
        )
        probability = math.exp(logarithm)
        if probability > 0:
            probabilities[str(rank)] = probability
    return probabilities


def holm_adjust(pvalues):
    ordered = sorted(range(len(pvalues)), key=lambda index: pvalues[index])
    adjusted = [0.0] * len(pvalues)
    running = 0.0
    for position, index in enumerate(ordered):
        running = max(running, (len(pvalues) - position) * pvalues[index])
        adjusted[index] = min(1.0, running)
    return adjusted


def summarize(cases, records):
    summaries = []
    for case in cases:
        samples = [record for record in records if record["case"] == case["name"]]
        structured = Counter(record["structured_rank"] for record in samples)
        reference = Counter(record["reference_rank"] for record in samples)
        n = len(samples)
        maximum = min(case["rows"], case["columns"])
        deficient = n - structured[maximum]
        reference_deficient = n - reference[maximum]
        null_probability = deficiency_probability(case["rows"], case["columns"])
        fisher_p = float(fisher_exact([
            [deficient, n - deficient],
            [reference_deficient, n - reference_deficient],
        ]).pvalue)
        theoretical_p = float(binomtest(deficient, n, null_probability).pvalue)
        variation = 0.5 * math.fsum(
            abs(structured[rank] - reference[rank]) / n
            for rank in set(structured) | set(reference)
        )
        summaries.append({
            **case,
            "maximal_rank": maximum,
            "unique_column_row_selections": len({record["selection_sha256"] for record in samples}),
            "structured_rank_histogram": dict(sorted(structured.items())),
            "reference_rank_histogram": dict(sorted(reference.items())),
            "theoretical_rank_probabilities": theoretical_rank_probabilities(case["rows"], case["columns"]),
            "structured_deficient": deficient,
            "reference_deficient": reference_deficient,
            "structured_deficiency_rate": deficient / n,
            "reference_deficiency_rate": reference_deficient / n,
            "theoretical_deficiency_probability": null_probability,
            "two_sample_total_variation": variation,
            "fisher_two_sided_p": fisher_p,
            "binomial_two_sided_p": theoretical_p,
        })
    fisher_adjusted = holm_adjust([row["fisher_two_sided_p"] for row in summaries])
    theory_adjusted = holm_adjust([row["binomial_two_sided_p"] for row in summaries])
    for row, fisher_p, theory_p in zip(summaries, fisher_adjusted, theory_adjusted):
        row["fisher_holm_p"] = fisher_p
        row["binomial_holm_p"] = theory_p
    return summaries


def write_results(directory, metadata, summaries, records):
    result = {"metadata": metadata, "cases": summaries}
    (directory / "results.json").write_text(
        json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8"
    )
    raw_fields = ["case", "trial", "structured_rank", "reference_rank", "selection_sha256"]
    with (directory / "rank_samples.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=raw_fields)
        writer.writeheader()
        writer.writerows(records)
    summary_fields = [
        "name", "rows", "columns", "trials", "structured_deficient",
        "reference_deficient", "structured_deficiency_rate",
        "reference_deficiency_rate", "theoretical_deficiency_probability",
        "two_sample_total_variation", "fisher_two_sided_p", "fisher_holm_p",
        "binomial_two_sided_p", "binomial_holm_p",
        "structured_rank_histogram", "reference_rank_histogram",
    ]
    with (directory / "rank_summary.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=summary_fields, extrasaction="ignore")
        writer.writeheader()
        for row in summaries:
            item = dict(row)
            for field in ["structured_rank_histogram", "reference_rank_histogram"]:
                item[field] = json.dumps(item[field], sort_keys=True)
            writer.writerow(item)
    parameters = metadata["parameters"]
    lines = [
        "SBHash LOCAL RANK EXPERIMENTS",
        json.dumps(parameters, sort_keys=True),
        "Matrix SHA-256: " + metadata["matrix"]["sha256"],
        "Global rank: " + str(metadata["matrix"]["global_rank"]),
        "Zero columns: " + str(metadata["matrix"]["zero_columns"]),
        "Projective repetitions: " + str(metadata["matrix"]["projective_repetitions"]),
        "Ranks are exact over F_5. References have independent uniform F_5 entries.",
        "Deficient means rank below min(rows, columns).",
        "Fisher compares deficiency frequencies with the simulated reference.",
        "The binomial test compares deficiency frequency with the exact random-matrix law.",
        "Holm adjustment is applied separately to each family of tests across all cases.",
        "The full rank histograms are descriptive; these p-values test deficiency frequency.",
        "The individual-block case is a census; its p-values are descriptive null diagnostics.",
        "Sampled subsets can overlap. This is one fixed public matrix, not independent public seeds.",
        "No conclusion about all subsets, adversarial search, or attack costs follows from these tests.",
        "",
    ]
    for row in summaries:
        lines.extend([
            f"{row['name']}: {row['rows']} x {row['columns']}, n={row['trials']}",
            "  H ranks: " + json.dumps(row["structured_rank_histogram"], sort_keys=True),
            "  Reference ranks: " + json.dumps(row["reference_rank_histogram"], sort_keys=True),
            f"  Deficient H/reference: {row['structured_deficient']}/{row['reference_deficient']}",
            f"  Null deficiency probability: {row['theoretical_deficiency_probability']:.12g}",
            f"  Fisher raw/Holm p: {row['fisher_two_sided_p']:.8g}/{row['fisher_holm_p']:.8g}",
            f"  Binomial raw/Holm p: {row['binomial_two_sided_p']:.8g}/{row['binomial_holm_p']:.8g}",
            "",
        ])
    reference_flags = [row["name"] for row in summaries if row["fisher_holm_p"] < 0.05]
    theory_flags = [row["name"] for row in summaries if row["binomial_holm_p"] < 0.05]
    lines.extend([
        "Cases flagged at family-wise alpha=0.05 against reference: " + json.dumps(reference_flags),
        "Cases flagged at family-wise alpha=0.05 against theory: " + json.dumps(theory_flags),
    ])
    text = "\n".join(lines) + "\n"
    (directory / "results.txt").write_text(text, encoding="utf-8")
    print(text, flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--instance", choices=["paper", "notebook"], default="paper")
    parser.add_argument("--trials", type=int, default=1000)
    parser.add_argument("--rectangular-trials", type=int, default=200)
    parser.add_argument("--seed", type=int, default=20261021)
    parser.add_argument("--matrix-seed", default="CONSTASH_PUBLIC_MATRIX_SEED")
    parser.add_argument("--workers", type=int, default=min(4, os.cpu_count() or 1))
    parser.add_argument("--max-attempts", type=int, default=64)
    parser.add_argument("--output", type=Path, default=Path("sbhash_local_rank_results"))
    args = parser.parse_args()
    if min(args.trials, args.rectangular_trials, args.workers, args.max_attempts) < 1 or args.seed < 0:
        parser.error("Trial counts, workers and attempts must be positive; the seed must be nonnegative")
    r, m = (528, 192) if args.instance == "paper" else (384, 256)
    parameters = {"p": P, "ell": ELL, "r": r, "m": m, "n": m * ELL, "s": math.ceil(r / 3)}
    parameters["q"] = m - parameters["s"]
    args.output.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    print("Generating public matrix: " + json.dumps(parameters), flush=True)
    columns, matrix_metadata = generate_matrix(args.matrix_seed, r, m, args.max_attempts)
    print("Accepted matrix: " + json.dumps(matrix_metadata), flush=True)
    cases = make_cases(r, m, args.trials, args.rectangular_trials)
    batches = [
        (case, first, min(first + 25, case["trials"]), args.seed)
        for case in cases for first in range(0, case["trials"], 25)
    ]
    records = []
    completed = Counter()
    if args.workers == 1:
        initialize_worker(columns)
        for batch in batches:
            rows = run_batch(*batch)
            records.extend(rows)
            case = batch[0]
            completed[case["name"]] += len(rows)
            if completed[case["name"]] == case["trials"]:
                print("Completed " + case["name"], flush=True)
    else:
        with ProcessPoolExecutor(
            max_workers=args.workers,
            mp_context=multiprocessing.get_context("spawn"),
            initializer=initialize_worker, initargs=(columns,),
        ) as executor:
            pending = {executor.submit(run_batch, *batch): batch[0] for batch in batches}
            for future in as_completed(pending):
                rows = future.result()
                records.extend(rows)
                case = pending[future]
                completed[case["name"]] += len(rows)
                if completed[case["name"]] == case["trials"]:
                    print("Completed " + case["name"], flush=True)
    order = {case["name"]: case["id"] for case in cases}
    records.sort(key=lambda row: (order[row["case"]], row["trial"]))
    metadata = {
        "instance": args.instance, "parameters": parameters, "matrix": matrix_metadata,
        "experiment_seed": args.seed, "rng": "NumPy PCG64 with SeedSequence([seed, case_id, trial]).spawn(2)",
        "reference_distribution": "independent uniform F_5 entries, matched dimensions, without rejection",
        "python_version": sys.version, "numpy_version": np.__version__, "scipy_version": scipy.__version__,
        "platform": platform.platform(), "workers": args.workers,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "total_structured_submatrices": len(records), "total_reference_matrices": len(records),
        "elapsed_seconds": time.perf_counter() - started,
        "scope": "single fixed seed; empirical sampling only; no proof of security or exhaustive exclusion of dependencies",
    }
    write_results(args.output, metadata, summarize(cases, records), records)


if __name__ == "__main__":
    main()
