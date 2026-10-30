# Frozen statement provenance

The [anchor manifest](../frozen-anchors.json) records three sealed, author-approved statements. Each implementation proof calls its corresponding complete provider theorem. The active export successors carry the suffix `_palomar2`; they preserve the original mathematical contracts and all three ABI hashes.

## Approbation

The inherited development record attributes approval of the mathematical interfaces to Igor Kortchemski on 28 October 2026. On 29 October 2026 the user approved the concrete export changes with “Approuve”, including licensing, migration and the narrow Challenge/Solution exceptions. [Approval](APPROVAL.md) records that scope and the later private GitHub verification request.

| Active anchor | Export | Contract |
| --- | --- | --- |
| `thm_main_v1_palomar2` | `Parking.tvDist_firstCoordsLaw_bounds` | One common constant for the two uniform bounds. |
| `thm_profile_v1_palomar2` | `Parking.tendsto_tvDist_firstCoordsLaw` | Every allowed sample sequence and finite, zero or infinite profile parameter. |
| `prop_decoupling_v1_palomar2` | `Parking.klDiv_tvDist_firstCoordsLaw_le` | Joint KL and TV inequalities for the same size and sample parameters. |

Zero-based `Fin n` indices and positive-natural size preserve the source interpretation. No theorem is split, weakened or given stronger premises. The approved successor changes license/descriptive comments and uses Lean `v4.35.0` with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; it does not change the Frozen mathematical source or proof assembly.

## Current verification

The [successor record](../evidence/frozen-successors.json) links each predecessor to its active anchor. Protected prefixes have new hashes because their comments changed; suffixes and mathematical contracts are unchanged. [Header evidence](../evidence/license-header-update.json) and [comment evidence](../evidence/frozen-comment-update.json) identify those separate steps.

On 29 October 2026, the author requested correction of the profile header's stale `DRAFT_SORRY` label to `SEALED`. The [maintenance record](../evidence/profile-status-comment-update.json) records this comment-only change and its updated source and prefix hashes. The anchor identity, mathematical contract, statement and proof are unchanged.

Both Challenge and Solution reproduce all three original approved ABI SHA-256 values under Lean 4.35. [Challenge fidelity](CHALLENGE-FIDELITY.md) lists the values and links the raw outputs. The implementation [kernel replay](../evidence/audit/kernel-replay.log) rechecks all 1,570 project constants, including these exports, with only `propext`, `Classical.choice` and `Quot.sound` reachable. A deliberately corrupted proof was rejected.

The manifest's empty `definition_closure` arrays are not an empty-closure assertion. The ABI probe follows actual project definitions and instances, and the separate [raw structural diagnostic](../evidence/closure-comparison.log) compares supporting proof bodies and private helpers. Neither is an official Comparator or full-preflight result. Hosted verification and the public-snapshot preflight are tracked in [Preparation](PREPARATION.md).

Historical Lean 4.34 anchors and checks remain under [evidence/history-4.34](../evidence/history-4.34/). Original reference projects and the verified development library remain unchanged.
