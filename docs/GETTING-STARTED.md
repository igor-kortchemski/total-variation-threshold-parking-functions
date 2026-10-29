# Getting started

[Overview](../README.md) · [Results](RESULTS.md) · [Proof guide](PROOF-GUIDE.md) · [Verification](VERIFICATION.md)

## Read without building

Start with the [paper-to-Lean correspondence](RESULTS.md). Each entry links to its Lean declaration and proof. The [notation guide](NOTATION.md) explains the probability laws and indexing conventions. GitHub displays the source without installing Lean; repository access is required while this repository is private.

## Install the prerequisites

The commands below use Bash on Linux or macOS. On Windows, use a Linux environment such as WSL for these shell scripts.

- **Git** to clone the repository and pinned dependencies.
- **elan**, which supplies `lean` and `lake` and selects the version in `lean-toolchain`. Follow the [official Lean installation guide](https://lean-lang.org/install/). VS Code with the official Lean 4 extension provides interactive proof inspection.
- **Python 3.9 or later** and **Ruby** for the source and metadata checks. They use their standard libraries; no Python package installation is required for the commands below.
- A working HTTPS connection for the initial toolchain, dependency, and Mathlib cache downloads.

The pinned environment is Lean **4.35.0** and Mathlib commit **`56a005855ea17e0b0958f73ec801ae140b0a1679`**. Transitive dependency revisions are recorded in [lake-manifest.json](../lake-manifest.json).

## Clone and build

```sh
git clone https://github.com/igor-kortchemski/total-variation-threshold-parking-functions.git
cd total-variation-threshold-parking-functions
scripts/compile-lock.sh lake exe cache get
scripts/compile-lock.sh lake build
```

While the repository is private, authenticate GitHub access before cloning; GitHub CLI users can run `gh auth login` and `gh auth setup-git`. The repository URL stays the same when visibility changes.

The first Lake invocation lets elan obtain the pinned Lean toolchain. `cache get` fetches the pinned dependencies and Mathlib's precompiled artifacts. `lake build` then builds the project, including all implementation modules and both interface modules. Three warnings about `sorry` in **Challenge.lean** are expected: they belong to its statement interface. Implementation proof holes are forbidden and checked separately.

Always run Lean and Lake through `scripts/compile-lock.sh`; it prevents simultaneous compilation in one checkout. To inspect the selected toolchain:

```sh
scripts/compile-lock.sh lean --version
```

Open this folder, rather than an individual file, in VS Code. Start with [Law.lean](../Parking/Law.lean) for the objects or a statement linked from [Results](RESULTS.md). The editor's “Go to Definition” follows the proof's dependencies.

## Run the implementation checks

After a successful build, run these commands sequentially:

```sh
python3 scripts/check-package.py
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb formalization.yaml
scripts/audit-project.sh
```

The package check compares source hashes and the three permitted Challenge placeholders, checks the pinned environment, and enforces the import boundaries. The source scan checks module headers and file lengths. The Ruby check validates the starter's metadata fields; it is not the complete Palomar schema validator.

The final script inventories all implementation declarations, checks their axiom dependencies, and replays their proofs in Lean's kernel. It also requires rejection of a deliberately invalid proof. It manages its own compile lock and removes its temporary probe. Its deterministic inventory is written under `evidence/audit/`; on an unchanged checkout it must match the tracked inventory.

## Time, storage, and fresh-checkout evidence

The [Build and audit workflow](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/build.yml) starts on a fresh Ubuntu 24.04 runner, without restored project artifacts or a GitHub Actions build cache. It executes the cache, build, and audit commands above, using an authenticated archive of the same Lean version instead of elan for bootstrap.

Each run records its exact commit, hardware, cache/build/audit durations, Lean archive size, and the final `.lake` disk footprint in its summary and `build-audit` artifact. Consult a **completed successful run** for measured values; local runtime varies with hardware and connection speed. The disk footprint includes dependencies and build products and is not a measurement of downloaded bytes. The workflow requires at least **20 GiB of free disk before installing Lean**; this is a CI allowance, not a measured minimum for local use.

## Troubleshooting

- **`lake` is not found:** finish the elan setup and restart the shell so its binary directory is on `PATH`.
- **Clone denied or repository not found:** confirm that GitHub is authenticated as an account with repository access.
- **A dependency or cache download fails:** check network access and available disk space, then rerun the cache command. Keep the pinned manifest and toolchain unchanged.
- **The compile lock waits:** another command may still be running. Read `.scratch/compile.lock/pid` and inspect that process before intervening; a permission error when inspecting it does not prove the lock is stale.
- **A proof fails or a check reports changed sources:** retain the error, exact commit, and output of the version command. Read the [verification scope](VERIFICATION.md) before comparing results from different revisions.

## Independent proof verification

The implementation audit above uses Lean's kernel. The separate [manual Comparator workflow](../.github/workflows/private-comparator.yml) checks the three recorded Challenge/Solution targets and their exports with additional checkers in its supported Linux sandbox. Its setup and exact results are explained in [Verification](VERIFICATION.md). Official Palomar full preflight is a separate operation on the final public commit.
