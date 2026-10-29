# Verification

[Overview](../README.md) · [Results](RESULTS.md) · [Getting started](GETTING-STARTED.md)

## What each check establishes

| Check | Scope | Where to inspect it |
| --- | --- | --- |
| Automatic build and audit | All 79 implementation modules plus Challenge and Solution build. Source and metadata constraints pass. All implementation declarations undergo an axiom-dependency audit and Lean-kernel replay, with an invalid-proof negative control. | [Build workflow](../.github/workflows/build.yml), [runs](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/build.yml) |
| Manual proof verification | The three declarations in `comparator.json`, including their concrete statement definitions, are compared between Challenge and Solution. The exported proofs are checked by Lean and NanoDa; con-ron is an additional advisory check. | [Comparator configuration](../comparator.json), [workflow](../.github/workflows/private-comparator.yml), [runs](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/private-comparator.yml) |
| Source correspondence review | Definitions, assumptions, endpoint cases, and the paper's proof routes are compared with the formalization. This is an AI-assisted source review, distinct from kernel checking. | [Results](RESULTS.md), [errata and deviations](ERRATA-AND-DEVIATIONS.md), [source review](../evidence/active-source-review.md) |
| Official Palomar full preflight | The official pipeline checks its exact submitted repository snapshot and configuration. | [Prepared workflow](../.github/workflows/palomar-preflight.yml); not yet run |

The additional lemmas, introductory consequences, and geometric remark are included in the implementation build and kernel audit. They are not separately selected targets of the three-result Comparator configuration. No independent human peer review or Palomar registration is claimed.

## Read the commit, not just the badge

The build badge follows the `main` branch's build workflow. Pull-request runs check GitHub's proposed merge commit. The proof-verification badge follows the latest manual run on `main`; it may describe an earlier commit than the current branch head. Open the run and inspect its SHA and report before attributing a result to a checkout.

The retained successful private proof-verification run is [run 40841476149](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/runs/40841476149), at commit [`fee7091b77e32a82b771207093f084de0d3bb67a`](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/tree/fee7091b77e32a82b771207093f084de0d3bb67a). Comparator, Lean, NanoDa, con-ron, the positive/negative controls, and source-integrity checks passed there. New runs carry their own exact source commit; this recorded result is not a claim about a later commit.

Build reports include the checked commit, step outcomes, timings, resource measurements, and logs. Comparator reports additionally identify the configuration, target declarations, tool pins, kernel outcomes, and source hashes. Download artifacts while available if you need a durable local record; the workflows specify their retention periods.

## Challenge and Solution

[Challenge.lean](../Challenge.lean) is the small statement interface intended for inspection. It defines the actual objects used in the results and contains exactly three authorized `by sorry` proof bodies:

- `Parking.tvDist_firstCoordsLaw_bounds`;
- `Parking.tendsto_tvDist_firstCoordsLaw`;
- `Parking.klDiv_tvDist_firstCoordsLaw_le`.

[Solution.lean](../Solution.lean) imports the complete proofs of the same declarations from the three [Frozen modules](FROZEN.md). “Frozen” means that the statement and its defining context are preserved while the proof is assembled through the corresponding provider. The implementation does not import Challenge. Comparator checks that Solution proves the declarations stated by Challenge, with the permitted axioms.

The implementation's allowed axioms are **`propext`, `Classical.choice`, and `Quot.sound`**. Its audit excludes Challenge's deliberate placeholders; it permits no implementation proof hole, custom axiom, or trusted-computation shortcut. [Challenge fidelity](CHALLENGE-FIDELITY.md) documents the statement and definition comparisons.

## Retained Lean 4.35 evidence

The existing [implementation audit](../evidence/audit/kernel-replay.log) covers **1,570 declarations: 1,477 theorems and 93 definitions**, with **62,604 reachable constants**. It reports only the three allowed axioms and rejects a corrupted proof. The [source manifest](../evidence/source-manifest.json) identifies the checked Lean sources. Future runs determine their own counts from their checked source.

The [full preparation record](PREPARATION.md) contains the build, source fidelity, frozen-interface hashes, and diagnostic evidence. Earlier Lean 4.34 results are retained under [historical evidence](../evidence/history-4.34/) and are not current toolchain verification. The local raw-closure diagnostic is distinct from the hosted Comparator check.

## Reproduce and interpret the results

Follow [Getting started](GETTING-STARTED.md) for the fresh-checkout build and full implementation audit. The [manual workflow](../.github/workflows/private-comparator.yml) supplies the Linux sandbox and authenticated toolchain inputs required for the standalone proof check. Its private-repository guard remains in force.

An incomplete, cancelled, or failed run does not establish a pass. A resource or bootstrap failure needs diagnosis before it can say anything about the proofs. The independent con-ron checker is advisory under the pinned policy; its reported acceptance or decline is separate from the mandatory Lean and NanoDa outcomes.

When the arXiv identifier becomes available, update the README, citation file, and mathematical-source metadata. The official Palomar full preflight must then use that final public commit before intake. Neither the private checks nor a full preflight constitute registry submission or registration.
