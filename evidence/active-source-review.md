# Active export source-fidelity review

Date: 2026-10-29. Result: **source-fidelity checks passed**.

This review compares the 79 implementation sources with the verified `Parking-paper` snapshot. All 79 baseline files still match `docs/reconstruction/final-source-hashes.json`. The reviewer read source and evidence only; no Lean or Lake process was launched.

## Implementation comparison

A fresh scanner removes nested block comments and line comments while preserving every other character, including whitespace. No executable string or quoted identifier required special handling. Exact comparison after the six reviewed proof edits accounts for every noncomment difference: 75 files are identical, and four files contain six edits across five declarations.

| File | Declaration | Review |
| --- | --- | --- |
| `Parking/Basic.lean` | `isParkingFunction_zero` | Same statement and counting argument. The all-zero filter is explicitly identified with `univ`, its cardinality is `n`, and the bound is `Nat.succ_le_of_lt j.isLt`. |
| `Parking/Law.lean` | `MeasurableSingletonClass` instance | Same class type, with the explicit subtype proof witness. Mathlib declares this class in `Prop`. The `MeasurableSpace` instance and all probability-law constructions are unchanged. |
| `Parking/Count.lean` | `card_castSucc_lt` | Removes the three redundant tactics after `congr 1`; preserves the filter-cardinality equality and statement. |
| `Parking/FirstCoordCount.lean` | `isParkingFn_iff_le_card` | Two removals after `congr 1`; preserves both threshold-shift directions of the parking characterization. |
| `Parking/FirstCoordCount.lean` | `sum_firstValueCount` | One removal after `congr 1`; preserves the fiber-sum counting argument. |

All six edits lie in proof bodies, after their declaration's `:=`. Exact equality everywhere else establishes that all theorem statement source and all data-bearing definition source are unchanged. The three Frozen implementation files are identical after comments are removed. No implementation `sorry`, `admit`, added `axiom`, unsafe declaration, native decision shortcut, or compiler-trust primitive was found.

The changes preserve the manuscript proof route at source level. They do not alter the breakpoint, reflection, Borel, occupation, log-concavity, Han, entropy, main-bound, profile, or geometric arguments. Whether the shortened `congr 1` proofs elaborate on the active toolchain is a separate build question.

## Challenge and Solution

The historical block inventory was used only to enumerate declarations, not as evidence of current hashes. Each of the 19 supporting declarations and three Frozen theorem signatures is a unique verbatim match in both its current implementation source and `Challenge.lean`, incorporating the two approved supporting-proof adaptations.

The remaining executable Challenge text consists of nine public Mathlib imports, namespace/section/open commands, the three approved `by sorry` bodies, and exactly four reviewed `auxLemmasExt` cache resets. No project import, extra assumption, hidden proof hole, or additional executable command remains. `Solution.lean` consists only of `module` and the three approved public Frozen imports.

Lean 4.35's `Lean/Meta/Tactic/AuxLemma.lean` declares this extension as a local cache and documents that it is not serialized in `.olean` files. Resetting it clears the type-to-helper-name lookup, without changing or deleting existing declarations or changing kernel rules. This can affect auxiliary proof reuse and helper identity; successful structural comparison must still be established independently.

## Evidence and limits

[Machine-readable checks](active-source-review.json) record all baseline/current SHA256 hashes, noncomment hashes, exact six edits, the 22 block matches, and hashes of active configuration and adaptation evidence. Inputs were rehashed for stability before writing the report. No unexpected source change was found.

This reviewer did not author the six proof edits or four cache resets, but previously contributed underlying library proofs and export comment/license changes. This is an independent review of the current adaptations, not independent human peer review.

This result establishes textual scope and argument fidelity. Identical source can elaborate differently across toolchains. It does not certify current Lean 4.35 compilation, generated constant structure, axiom closure, kernel replay, Comparator, NanoDa, or the official release pipeline. Those results require their own current evidence.
