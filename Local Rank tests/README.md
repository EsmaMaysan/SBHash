# SBHash local rank experiments

We reproduce the supplied matrix and measurements.

We implemented exact modular rank in `rank\_mod\_p\_square` and uses it in `\_candidate\_has\_full\_rank\_minor` to accept matrices whose first `r` columns are independent. 

The parameters are `(p, ell, r, m) = (5, 64, 384, 256), with `n=12288`, `s=176`, and `q=16`. The notebook rejects duplicate columns. The new generator checks the full row rank condition and projective uniqueness. If the first square minor is singular, it examines further columns rather than rejecting an otherwise acceptable matrix.

The notebook's SHAKE-256 column derivation, index encoding, rejection of byte 255, are preserved byte for byte. With the final dimensions, candidate 0 is accepted and its first square minor is already invertible.

## Reproduce

Tested with Python 3.12.14, NumPy 2.3.5, and SciPy 1.17.0.

```bash
python -m pip install -r requirements.txt
python sbhash\_local\_rank\_tests.py --workers 4 --output reproduced\_results
```

The defaults perform the delivered final-parameter campaign. Set `--workers 1` for serial execution; the sampled subsets and ranks are unchanged. Worker functions are protected for normal Python execution on Windows.

For an initial small run:

```bash
python sbhash\_local\_rank\_tests.py --trials 2 --rectangular-trials 1 --workers 1 --output quick\_results
```

Every run still checks all 192 individual blocks. To run the same test design at the old dimensions, use `--instance notebook`. 

## Files

* `sbhash\_local\_rank\_tests.py`: complete executable implementation.
* `results/results.txt`: readable results and interpretation limits.
* `results/rank\_summary.csv`: one row per configuration, histograms and statistical comparisons.
* `results/rank\_samples.csv`: all 8792 paired rank observations and subset checksums.
* `results/results.json`: metadata, exact parameter choices, RNG details, full rank histograms, theoretical rank probabilities and p-values.
* `local\_rank\_paragraph.tex`: suggested replacement paragraph reporting this campaign. Its repository sentence assumes the code and data have been uploaded.

## Sampling design

There are 16 configurations and 8792 public-matrix submatrices, with one independent random reference of matching dimensions per submatrix:

* Uniform column subsets of sizes 64, 192 and 384: 200 trials each.
* Uniform column subsets of sizes 527, 528 and 529: 1000 trials each.
* All 192 individual blocks, each with all 528 rows and 64 columns.
* Uniform subsets of 2, 4, 8 and 9 complete blocks, with all rows: 200 trials each.
* Uniform subsets of 1, 2, 4 and 8 complete blocks, restricted to uniform row subsets to form squares of sizes 64, 128, 256 and 512: 1000 trials each.
* Two distinct random columns per block, across all 192 blocks: 200 trials.

Selections are made without replacement within each trial; selections across trials can overlap. The individual-block case is a census. The matrix is fixed rather than regenerated under independent public seeds.

All ranks are computed by Gaussian elimination in F\_5, using exact integer arithmetic. The code does not use floating-point real or complex matrix rank. Each simulated reference has independent uniform entries in F\_5 and is not screened for full rank.

## Measured results

The public matrix has rank 528, no zero columns, and no proportional pair of columns. Every individual 528-by-64 block has rank 64.

|Uniform column subset|Trials|Rank-deficient in H|Rank-deficient references|Fisher p after Holm correction|
|-|-:|-:|-:|-:|
|528 x 527|1000|35|56|0.501717|
|528 x 528|1000|238|230|1.000000|
|528 x 529|1000|57|49|1.000000|

For the 528-by-528 subsets of H, the ranks are 526 in 3 samples, 527 in 235 samples and 528 in 762 samples. The matched references have counts 3, 227 and 770, respectively. The theoretical probability that a uniform square matrix of this size over F\_5 is singular is 0.239667204129.

The square block projections have deficiency counts 240, 242, 229 and 252 out of 1000 for sizes 64, 128, 256 and 512, respectively; the matched reference counts are 261, 227, 240 and 231. All other tested rectangular configurations attain the maximal possible rank in every sample, in both populations.

For uniform a-by-b matrices over F\_5, the full-rank probability is the product of `(1 - 5^(-j))` for `j = abs(a-b)+1, ..., max(a,b)`. The implementation also records the theoretical probabilities for every representable rank.

The primary comparison with simulated references uses two-sided Fisher exact tests on the counts of maximal rank versus deficient rank. A separate diagnostic uses exact two-sided binomial tests against the theoretical rank-deficiency probability. Holm correction is applied separately across the 16 Fisher tests and the 16 binomial tests. The histograms and total variation distances compare the full empirical distributions descriptively; the reported p-values specifically test deficiency frequency.

No comparison is significant after correction at 5% within either family. The smallest adjusted Fisher p-value is 0.501717466; the smallest adjusted theoretical-binomial p-value is 0.547665050. The 528-by-527 comparison has an unadjusted Fisher p-value of 0.031357342, so it would be inaccurate to say that every unadjusted p-value exceeds 0.05. This case has fewer deficient submatrices than the reference.

Extremely small theoretical probabilities can underflow in binary floating-point output. For example, the uniform 528-by-64 deficiency probability is approximately 1.190852565886E-325; the numeric JSON/TXT field rounds to zero. That zero is not a mathematical impossibility statement.

## Verification performed

* Exhaustive comparison of all 625 two-by-two matrices over F\_5 with an independent scalar elimination routine; the exact rank counts are 1, 144 and 480.
* Cross-check of 867 small random rectangular integer matrices, including negative entries, and constructed dependent matrices.
* Explicit check of a matrix with real rank 2 but rank 1 modulo 5.
* Agreement of the theoretical rank formula with exhaustive two-by-two counts and normalization at the experimental dimensions.
* Byte-for-byte column compatibility with the supplied notebook at r=384 and r=528, including a nonzero matrix candidate counter.
* Independent reconstruction of the full final-parameter matrix using the notebook generator, with the same SHA-256 digest.
* Independent agreement with the notebook's modular rank routine on large rectangular and square matrices.
* Explicit tests for zero/proportional columns and acceptance of a globally full-rank matrix whose first square minor is singular.
* Exact agreement of all 214 smoke-run observations with the corresponding observations in the four-worker full run.
* Integrity checks of all counts, trial indices, histograms and source checksums; verification that the Python source has no comments.

## Provenance

* Public matrix SHA-256: `808bf91f34fdeba491c3c05f7267344ef96a3410bb92f2162af101eaf52a83c9`.
* SHA-256 layout: uint8 entries in block-column-coordinate order, shape `(192, 64, 528)`.
* Experiment seed: `20261021`. The script records independent PCG64 selection/reference streams for every case and trial.
* Source notebook SHA-256: `6d688d997c67f0abca83fd4feb85d1778292d664870771f6347ffbdb7495c9ab`.
* Source manuscript SHA-256: `784a164d7f040fc83f71295ee8b8ee0f80612bd1cb446d299df0f73aa4e72823`.
* Packaged script SHA-256: `86a0c951cd51827cdcbb767e948e8aa3c5c61f105a689e98a03e378fa46ff88f`.
* Measurement script SHA-256 before the name change: `a8fe5317fc77faf97e76e887226bb9e56dfc07470e078e05e0ad521856e60918`.



