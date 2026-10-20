# SBHash: Machine-checked collision-reduction proof

This reproducibility package accompanies the manuscript **Syndrome-Based Hashing over Prime Fields**. It contains the EasyCrypt formal model, a WSL/Ubuntu installation guide, and instructions for checking the proof locally.

The EasyCrypt development proves that a whole-hash collision implies a collision in the round function and then in the compression function, **under the explicit interface assumptions of the formal model**. It does *not* formalize the concrete matrix multiplication, prove regular syndrome-decoding hardness, or prove a concrete 128-bit security level.

## Archive contents

* `SBHash.ec` — EasyCrypt specification and proof source.
* `README.md` — Overview, proof scope, and reproducibility checklist (this file).
* `INSTALLATION\_WSL\_EN.md` — Step-by-step WSL/Ubuntu installation and compilation guide.

## Model and parameters

The instantiated parameters are

|Parameter|Value|Meaning|
|-|-:|-|
|`p`|5|Prime field size|
|`ell`|64|Number of positions per sparse block|
|`r`|528|Chaining-state dimension over `F\_5`|
|`m`|192|Number of alphabet symbols per compression input|
|`s`|176|Number of bytes/symbols for the packed state|
|`q`|16|Fresh message symbols per compression call|

The model has `s + q = m`, `2\*m < r`, and `16\*q = 256`. A round input concatenates the state encoding and a fresh message block. The compression function is represented by an abstract operation with a validity interface.

The key lemmas are:

```text
round\_collision\_implies\_compression\_collision
hash\_collision\_implies\_round\_collision
hash\_collision\_implies\_compression\_collision
```

## Assumptions and limits of formal verification

The source explicitly declares these interface axioms (among its definitions and proved lemmas):

```text
symbol\_of\_byte\_spec
pack\_state\_valid
pack\_state\_injective
compress\_valid
iv\_valid
preprocess\_valid
preprocess\_aligned\_suffix\_free
```

In particular, `preprocess\_aligned\_suffix\_free` is **assumed inside EasyCrypt**. The paper argues this property mathematically for the preprocessing design, but the uploaded EasyCrypt development does not establish it from a fully implemented SHA-2-style padding/scheduling routine. Similarly, `pack\_state\_injective` is axiomatized rather than proved from a concrete byte-list packing implementation. The results are conditional on these assumptions.

## Quick proof check under WSL

For initial installation and full instructions, follow `INSTALLATION\_WSL.md`. From an Ubuntu terminal with the `easycrypt` OPAM switch already installed and configured:

```bash
eval "$(opam env --switch=easycrypt)"
easycrypt compile SBHash.ec
printf 'EasyCrypt exit code: %s\\n' "$?"
```

A return code of `0` indicates that this invocation completed successfully; save the output and ensure the intended theorem statements were checked under the expected solver configuration. If EasyCrypt or its prover is unavailable, follow the installation guide first.

## Reproducibility



For better reproducibility, archive the actual version manifest and compilation transcript from the author's WSL system:

```bash
cat /etc/os-release
opam --version
opam switch show
opam list --installed --short
opam pin list
easycrypt why3config
easycrypt compile SBHash.ec 2>\&1 | tee easycrypt-compile.log
```

If a pipeline is used, inspect its exit status carefully (for example, `set -o pipefail` before running the last command). This archive does not contain such a log or a lockfile.

## Suggested statement for the manuscript

> The EasyCrypt source code establishing the collision-preservation reduction, together with WSL/Ubuntu setup and proof-checking instructions, is provided in the supplementary reproducibility archive. The formal reduction is verified under the interface assumptions stated in the manuscript; the hardness of the underlying regular syndrome-decoding problem is assessed separately.

