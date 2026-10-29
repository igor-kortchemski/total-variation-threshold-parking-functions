# Challenge fidelity and closure checks

[Challenge.lean](../Challenge.lean) is an active Lean 4.35 module. It imports nine Mathlib modules, copies 19 supporting declarations and the three approved theorem signatures, and contains exactly three authorized `by sorry` bodies. [Solution.lean](../Solution.lean) imports the three complete Frozen proofs. Neither Solution nor any implementation module imports Challenge.

## Concrete mathematical interface

The Challenge retains the original namespace, declaration order, exposure attributes, relevant scopes and actual probability constructions. Its [source-block inventory](../evidence/challenge-source-blocks.json) records unique verbatim matches against the current implementation sources.

| Retained declarations | Mathematical role |
| --- | --- |
| `isParkingFunction`, `ParkingFunction` | Finite prefix-count condition and subtype of admissible words. |
| `isParkingFunction_zero`, `parkingFunction_nonempty` | Concrete all-zero witness for nonemptiness. |
| `DecidablePred`, `Fintype`, `Nonempty`, `MeasurableSpace`, `MeasurableSingletonClass` instances | Actual finite carrier and measurable structure. |
| `tvDist`, `uniformLaw`, `uniformParking` | Finite total variation and normalized counting law. |
| `firstCoords`, `firstCoordsLaw`, `uniformProduct` | Coordinate projection, parking pushforward and independent uniform law. |
| `firstCoord`, `marginal`, `marginalProduct` | One-coordinate pushforward and its independent product. |
| `profile` | Gaussian finite-parameter expression and value one at infinity. |

No abstract surrogate law or added measurability premise replaces these definitions. The 79 implementation files differ from the verified development snapshot only by authorized comments and six proof edits in four files. [Source review](../evidence/active-source-review.md) verifies that all statement source and data-bearing definitions remain unchanged.

## Three preserved signatures

| Export | Scope | Approved and current ABI SHA-256 |
| --- | --- | --- |
| `Parking.tvDist_firstCoordsLaw_bounds` | One common $C\ge1$ before every $n\ge2$ and $1\le k\le n$; both bounds remain in one conjunction. | `ff544decb2bedb055a042a7735665ce805574dedd767c506f8f39eb227d814aa` |
| `Parking.tendsto_tvDist_firstCoordsLaw` | Every sample-length sequence with $1\le k_n\le n$ and every finite, zero or infinite scale parameter; the original extended-real convergence hypothesis. | `b47583fb8752c011849eb5cf38b396134981b271bed5c4c3d35303fb02b87d1a` |
| `Parking.klDiv_tvDist_firstCoordsLaw_le` | Every $n\ge2$ and $1\le k\le n$, including $k=1$; joint extended-real KL and real TV inequalities. | `bdd2284b1f51d6ad604ab262deafb182f2914b170650bf6944469300fc3e2aaf` |

All three signatures are copied verbatim, including binder order, casts, endpoints and final `:=`. Both current [Challenge ABI output](../evidence/challenge-abi-raw.txt) and [Solution ABI output](../evidence/solution-abi-raw.txt) reproduce the original approved hashes. Empty `definition_closure` arrays in the [manifest](../frozen-anchors.json) do not mean the semantic closure is empty: the ABI probe traverses the actual project definitions and instances.

## Supporting proofs and module boundaries

Two approved supporting-proof spellings occur identically in Challenge and implementation: the zero-word theorem explicitly identifies its filter with `univ`, and the measurable-singleton proposition uses `Subtype.instMeasurableSingletonClass`. Neither changes a statement, data-bearing instance or probability law. [Adaptation evidence](../evidence/structural-proof-adaptations.json) records both edits.

Challenge also resets `Lean.Meta.auxLemmasExt` exactly four times at the original module boundaries. Lean 4.35 declares this as a local type-to-helper-name cache that is not serialized in `.olean` files. Clearing it reproduces the separation of auxiliary-proof reuse between imported modules; it does not change or remove declarations, introduce assumptions or alter kernel checking. Generated private names and proof bodies still require comparison.

## Verification levels

The active Challenge and Solution both build. The [raw closure diagnostic](../evidence/closure-comparison.log) imports them into separate full-value environments, compares each target's name, universe parameters and type, then compares every reachable supporting `ConstantInfo` exactly. It uses Lean's traversal for primitives, inductives, constructors and recursors. Only the three designated target proof bodies are omitted; no private name or supporting proof is filtered.

The result is three matching target records and 34,347 matching supporting constants, including 24,773 supporting theorem bodies and 4,036 private names. The diagnostic does not replace LeanExport serialization, official Comparator policy, independent kernel replay or the full Palomar preflight. [Implementation kernel replay](../evidence/audit/kernel-replay.log) is a separate completed local check.

The authorized [private hosted verification](https://github.com/igor-kortchemski/Parking-paper-palomar/actions/workflows/private-comparator.yml) records its actual result for the run's source commit. The official full preflight, public release and Palomar intake remain outside the completed checks. See [Preparation](PREPARATION.md) and [Approval](APPROVAL.md).
