# SBHash security estimators

## Scope

This directory contains computational estimators for the coefficient-valued regular syndrome-decoding problems associated with the SBHash compression function. The fixed instance is

|Parameter|Value|
|-|-:|
|Field size, `p`|5|
|Regular block length, `ell`|64|
|Syndrome dimension, `r`|528|
|Number of regular blocks, `m`|192|
|Public-matrix width, `n = m \* ell`|12288|
|Encoded-state symbols, `s = ceil(r / 3)`|176|
|Fresh scheduled symbols per round, `q = m - s`|16|

All computational cost values are base-2 logarithms. Repetition exponents, total estimator work factors, and attacker-favorable benchmarks are distinct quantities and should not be interpreted as interchangeable measures.

## Requirements

Python 3.10 or newer is recommended. Install the external dependency with

```sh
python -m pip install -r requirements.txt
```

The main computation uses the Python standard library and NumPy. The supplied RSD estimators do not use an actual syndrome-decoding solver.

## Reproducing the numerical comparisons

From this directory, run

```sh
python reproduce\_table1.py --output security\_estimates.csv
```

This reruns the principal available estimators for the fixed instance, writes the computed costs and optimized parameters to `security\_estimates.csv`, and compares them numerically with the rounded reference values in `reference\_table1.csv`. The full run includes a finite unrestricted Regular-ISD scan, the two-list enumeration scan, the hybrid linearization/Wagner scan, and the one-round Hilbert-series model; it can take several minutes depending on the machine.

A shorter diagnostic run is

```sh
python reproduce\_table1.py --quick --output security\_estimates\_quick.csv
```

Rows with no source-based recomputation contain a blank `recomputed\_log2\_cost`. The representation-attack row reruns a selected fixed profile rather than the full global search.

## Methods

### Direct regular collision decoding

For `m0` active blocks, let `r = f\*m0 + b` with `0 <= b < m0`. The number of locally admissible difference vectors is `D\_p(t) = 1 + t(p-1) + binom(t,2)(p-1)^2`. The balanced block profile gives `A\_p = D\_p(f)^(m0-b) D\_p(f+1)^b`. Scalar-orbit counting yields the sparse-regime projective repetition exponent `r log2(p) - log2(A\_p - 1) + log2(p-1)`. The driver evaluates this expression in logarithmic arithmetic; subtracting one is numerically negligible at the concrete parameters.

### Anchored linearization

An invertible `r x r` pivot submatrix by itself has no nonzero homogeneous kernel vector. The model uses `h <= m-1` pivot blocks and one additional block carrying a fixed nonzero residual syndrome. Reconstructed coefficients are approximately uniform over the nonzero pivot vectors, and the exponent is `log2(p^r-1) - log2(A\_lin-1)` in the balanced finite-block model. The driver uses the asymptotically equivalent logarithmic expression at the concrete parameters. An unanchored homogeneous model is not used.

### Regular-ISD collision attack

`p\_ary\_regular\_isd\_optimizer\_unrestricted.py` implements the unrestricted finite-block BLPS-style two-list optimization. Local difference counts, occupied-block completion counts, projective scalar-orbit handling, list capacities, rank probabilities, and list costs are included in its model. For the fixed instance, the optimum reported by this implementation is at `m0=192`, `lambda=61`, and `x=11`. `p\_ary\_regular\_isd\_optimizer.py` retains a separate balanced-profile implementation useful for binary BLPS comparisons.

### Linearization combined with generalized birthday

`p\_ary\_linearization\_wagner\_optimizer.py` searches pivot-block counts `h`, eliminated syndrome dimension `rho`, and Wagner depth `nu`. It requires a nonzero residual solution. Reconstruction is charged according to the locally admissible pivot-coefficient probability, and residual list feasibility is checked. The pure Wagner case uses `h=rho=0`. Work and memory are tracked separately.

### Preimage decoding

`p\_ary\_regular\_prange\_optimizer.py` evaluates the probability that a decoded pivot vector has exactly one nonzero coordinate in every block. `p\_ary\_regular\_isd\_preimage\_enum.py` optimizes finite coefficient-aware two-list enumeration and regular pivot completion. `p\_ary\_regular\_isd\_enum\_unrestricted.py` provides an additional unrestricted enumeration implementation. These are heuristic algorithm-cost estimates for compression-preimage instances, not claims that full iterated-hash preimages are equivalent to uniform compression-preimage instances.

### Representation-based decoding

`p\_ary\_representation\_combinatorics.py` calculates finite blockwise representation multiplicities. `p\_ary\_regular\_isd\_rep\_fixed\_profile.py` optimizes the cost for a specified `(lambda, u, R\_U)` profile. `p\_ary\_regular\_isd\_rep\_global\_search.py` and `p\_ary\_regular\_isd\_rep\_fast\_search.py` perform resumable profile scans; `p\_ary\_regular\_isd\_rep\_validation.py` provides local combinatorial checks. The driver independently reevaluates the published candidate profile `(lambda=297, u=122, R\_U=0)` with `tau\_slack=8` and reports its cost, but it does not repeat the entire global parameter scan. This row is explicitly marked `fixed-profile rerun only`, so the calculation validates the cost of a candidate rather than its global optimality. For a new global search, use the separate resumable drivers and complete their coarse and refinement stages.

### Algebraic and hybrid RSD

`p\_ary\_algebraic\_rsd\_estimator.py` implements the one-round Hilbert-series model with finite zero-position guessing and an optimistic dense-linear-algebra exponent `omega=2`. Its solving-degree estimates depend on a semi-regularity assumption that has not been established for this concrete instance. They are conditional estimates rather than provable lower bounds on algebraic attacks.

`official\_large\_field\_rsd\_benchmark.py` evaluates the finite large-field AGB 2.0 and hybrid RSD benchmark models at `n=m\*ell`, `k=n-r`, `h=m`, and block length `ell`. These are computational reimplementations of published algorithmic cost models, not formal certifications of optimality across all algebraic algorithms.

### Rep-MO comparison

The attacker-favorable Rep-MO figure is provided in `reference\_table1.csv` for comparison. Search outputs are provided under `data/repmo\_free\_nn\_stageA.csv` and `data/repmo\_free\_nn\_refine.csv`, but a self-contained source program that independently reconstructs the full nearest-neighbor, structured-residual correction, and regular-completion estimate is not part of this directory. The numerical value is **not** claimed as independently recomputed from source. In particular, a `p`-ary Hamming-ball volume by itself does not establish the probability of an admissible correction.

## Output interpretation

The output CSV contains `paper\_log2\_cost`, `recomputed\_log2\_cost`, `difference\_bits`, and `status`. The original comparison targets are rounded to two decimal places, so differences smaller than approximately 0.005 bits can result solely from rounding. The collision-work minimum and the preimage-work minimum are minima only over the assessed algorithm families and models. Memory requirements, including the large Regular-ISD list estimates, must be considered separately when interpreting practicality.

## Source inventory

|File|Function|
|-|-|
|`reproduce\_table1.py`|Fixed-instance driver and CSV comparison|
|`p\_ary\_regular\_isd\_optimizer\_unrestricted.py`|Coefficient-valued collision Regular-ISD|
|`p\_ary\_regular\_isd\_optimizer.py`|Balanced BLPS-style Regular-ISD variant|
|`p\_ary\_linearization\_wagner\_optimizer.py`|Hybrid linearization/Wagner and pure Wagner|
|`p\_ary\_regular\_prange\_optimizer.py`|Regular-Prange preimage decoding|
|`p\_ary\_regular\_isd\_preimage\_enum.py`|Finite coefficient-aware preimage enumeration|
|`p\_ary\_regular\_isd\_enum\_unrestricted.py`|Alternative unrestricted enumeration|
|`p\_ary\_representation\_combinatorics.py`|Representation multiplicities and small checks|
|`p\_ary\_regular\_isd\_rep\_fixed\_profile.py`|Fixed-profile representation work factor|
|`p\_ary\_regular\_isd\_rep\_global\_search.py`|Resumable global profile search|
|`p\_ary\_regular\_isd\_rep\_fast\_search.py`|Coarse-to-fine representation search|
|`p\_ary\_regular\_isd\_rep\_validation.py`|Representation-profile diagnostics|
|`p\_ary\_algebraic\_rsd\_estimator.py`|Hilbert-series model and zero-position guessing|
|`official\_large\_field\_rsd\_benchmark.py`|AGB 2.0 and hybrid RSD benchmark models|
|`reference\_table1.csv`|Rounded comparison targets from the manuscript|
|`security\_estimates.csv`|Measured output from the full fixed-instance driver|
|`data/repmo\_free\_nn\_stageA.csv`|Saved free-nearest-neighbor coarse optimization records|
|`data/repmo\_free\_nn\_refine.csv`|Saved free-nearest-neighbor refined optimization records|
|`data/regular\_isd\_r528\_m192.csv`|Saved Regular-ISD ranked optimization records|

## Limitations

The scripts implement complexity estimators and finite combinatorial optimizations. They do not generate a public SBHash matrix, find actual cryptographic collisions or preimages. The models include distributional, list-independence, semi-regularity, and algebraic-cost assumptions as described above. The results should be reported as estimates within the stated attack models. 

