# Installing and checking SBHash with EasyCrypt on Windows Subsystem for Linux (WSL)

This guide documents the installation and practical steps needed to compile `SBHash.ec`, for the supplementary materials of **Syndrome-Based Hashing over Prime Fields**.

Follow the official EasyCrypt documentation if tool versions have changed: [https://github.com/EasyCrypt/easycrypt/blob/main/INSTALL.md](https://github.com/EasyCrypt/easycrypt/blob/main/INSTALL.md).

## 1\. Install or open Ubuntu under WSL

If WSL has not been installed, open **PowerShell as Administrator** on Windows and run:

```powershell
wsl --install
```

Restart Windows if prompted, open Ubuntu, and complete the first-run Linux account setup. Skip this step if Ubuntu under WSL is already available. All remaining commands must be executed in the **Ubuntu terminal**, not PowerShell.

## 2\. Install basic system packages

```bash
sudo apt update
sudo apt install -y opam git build-essential unzip
```

`opam`, `git`, and `build-essential` reproduce the base package-installation approach from the earlier instructions; `unzip` is an added convenience for extracting the archive. Depending on the Ubuntu version and current EasyCrypt dependencies, OPAM may request additional system packages.

## 3\. Set up OPAM and an EasyCrypt switch

```bash
opam --version
opam init
opam switch --empty create easycrypt
opam switch set easycrypt
eval "$(opam env)"
```

Follow the prompts from OPAM. The dedicated switch separates this installation from other OCaml projects. We used a switch named `easycrypt`. If a switch with that name already exists, select it instead of recreating it.

## 4\. Install EasyCrypt from its official Git repository

```bash
opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git
opam install --deps-only easycrypt
opam install easycrypt
```

These commands follow the Git-pin installation approach. Because the pin is to a moving repository rather than an immutable commit, a new installation may fetch a different version from the one previously used. For strictly reproducible builds, pin an exact verified commit and save the OPAM package versions.

## 5\. Install an SMT solver and configure Why3

The historical installation used:

```bash
opam install alt-ergo
eval "$(opam env)"
easycrypt why3config
```

A later upstream EasyCrypt installation guide mentioned Alt-Ergo `2.6.0` for its contemporary Why3 version. If using newer EasyCrypt/Why3, consult their current installation instructions rather than forcing an old solver version. An alternative, only when supported by the installed packages, is:

```bash
opam install alt-ergo.2.6.0
easycrypt why3config
```

## 6\. Extract the archive and compile the formal proof

From an Ubuntu directory containing `SBHash\_EasyCrypt.zip`:

```bash
unzip SBHash\_EasyCrypt.zip -d sbhash-easycrypt
cd sbhash-easycrypt
eval "$(opam env --switch=easycrypt)"
easycrypt compile SBHash.ec
printf 'EasyCrypt exit code: %s\\n' "$?"
```

If you already extracted the archive, go directly to the folder containing `SBHash.ec`. 

A return code of `0` confirms that the command completed successfully in this environment. Check the console output for diagnostics and verify that required provers were configured.

## 7\. Collect a version manifest and compilation evidence

Run these commands in the working WSL setup and save the output:

```bash
cat /etc/os-release
opam --version
opam switch show
opam list --installed --short
opam pin list
easycrypt why3config
```

To save compilation output while preserving a meaningful failure status:

```bash
set -o pipefail
easycrypt compile SBHash.ec 2>\&1 | tee easycrypt-compile.log
printf 'Proof-check pipeline exit code: %s\\n' "$?"
```



## 8\. What the proof verifies

The formal model establishes, under explicit interface axioms,

```text
Collision(Hash) => Collision(Round) => Collision(Compression)
```

The proof checks a **collision-preservation reduction**. Specifically, several properties of concrete preprocessing, state packing, and compression validity are assumed in the EasyCrypt model.

