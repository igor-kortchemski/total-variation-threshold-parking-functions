# Approved export and private verification scope

On 29 October 2026, the user replied **“Approuve”** to the concrete export-only proposal. This applies to the export successor; the verified development library and both original reference projects remain unchanged.

1. **Environment:** migrate from Lean `v4.34.0` to `v4.35.0` with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, make necessary proof-compatibility repairs without changing mathematical meanings, rebuild and recompute definition/statement ABI evidence.
2. **License and attribution:** apply Apache-2.0 to the author's export code, including the retained parallel-formalization components within the described redistribution scope. Preserve author/year notices and attribution. Exclude manuscript source, bibliography and PDF. Basic/Law and Frozen header changes are authorized export successors, not changes to the originals.
3. **Challenge:** materialize exactly three proof placeholders in `Challenge.lean`, for `Parking.tvDist_firstCoordsLaw_bounds`, `Parking.tendsto_tvDist_firstCoordsLaw` and `Parking.klDiv_tvDist_firstCoordsLaw_le`. Keep imports Mathlib-only and preserve actual laws and signatures. No implementation proof may acquire a hole or new axiom.
4. **Solution:** allow only `Solution.lean` to import the three complete Frozen modules. Solution must not import Challenge; other provider/Frozen import restrictions remain in force.
5. **Validation:** activate the configuration and metadata, then check source/definition fidelity, successor ABIs, build, axiom closures and kernel replay. Supported Linux verification is needed for Comparator/NanoDa; the official full preflight additionally requires a separately authorized public snapshot.

The root [LICENSE](../LICENSE) is the approved Apache-2.0 text. [License-header evidence](../evidence/license-header-update.json) records its application to all 79 production headers, preserving every byte after each initial comment at that step. [Proof adaptations](../evidence/structural-proof-adaptations.json), [toolchain repairs](../evidence/toolchain-proof-repairs.json), and [source review](../evidence/active-source-review.md) account separately for six later proof edits across four files. Four Challenge cache resets reproduce original module boundaries without changing declarations or kernel rules. The Frozen `_palomar2` successors preserve all three approved statement/definition ABI hashes.

## Subsequent private GitHub authorization

The user then specified **“for comparator I prefer a private thing on github”**. In the context of the requested verification, this authorizes creating `igor-kortchemski/Parking-paper-palomar` as a private repository, pushing the prepared export and running the necessary manual private verification workflow. No further permission is needed for those actions within this scope.

The repository must remain private. This authorization does not permit a visibility change, public release, public archive upload, Palomar intake, registration, or redistribution of excluded manuscript files. A private hosted verification report is distinct from the official public-snapshot full preflight.

[Preparation](PREPARATION.md) records completed local Lean 4.35 checks and the private hosted evidence. Each hosted result must name the exact source commit and retained evidence. Approval is not a verification result or an assertion of independent human peer review.

## Repository rename

On 29 October 2026, the user chose `total-variation-threshold-parking-functions` and requested changing the existing repository name. The same private repository is now `igor-kortchemski/total-variation-threshold-parking-functions`; its repository identity, Git history and verification runs are retained. Active links and the local Git remote follow the new name. Historical authorization and verification receipts retain the original name and checked commit. This rename does not authorize a visibility change or Palomar submission.

## Reader documentation and automatic CI

On 29 October 2026, the user approved the proposed README, complete paper-to-Lean correspondence, notation and proof guides, quick-start validation, citation file, and automatic build checks with “Ok let's go for everything we said”. This authorizes the corresponding documentation and CI changes, necessary private commits and pushes, and validation runs. Automatic build checks on pushes and pull requests are part of this request. The existing mathematical sources, pinned environment, and proof-verification policy are retained. The repository remains private; the arXiv identifier is to be added later, before the final public Palomar preflight. Public visibility, arXiv submission, Palomar intake, and registration are not performed as part of this preparation.
