# Errata and deviations

This record covers the supplied parking-function manuscript identified in [Provenance](PROVENANCE.md). Locations use its stable labels and theorem numbers. An erratum means a demonstrated defect in the mathematical source; a supplied proof of a true omitted calculation is recorded as an elaboration. Counts are entries, not occurrences. No source error affecting Theorems 1.1, 1.2 or Proposition 1.3 is claimed.

| Source | Errata | Encoding or elaboration entries |
| --- | --- | --- |
| Parking-function manuscript | 0 | 6 |

## Errata

None identified in the reconstructed targets.

## Encodings and elaborations

1. **Parking words and all three main results.** Coordinates and values use zero-based `Fin n`. A Lean value $j$ encodes manuscript value $j+1$. The counting criterion is equivalent to the sorted parking criterion. See `Parking.isParkingFunction` in [Basic](../Parking/Basic.lean) and `Parking.isParkingFunction_iff_sort_le` in [PrefixProduct](../Parking/Paper/PrefixProduct.lean). The mathematical event is unchanged.
2. **Size and sequence domains.** Sizes use $n:\mathbb N_{>0}$; samples satisfy $1\le k\le n$. This avoids an impossible positive-sample hypothesis at $n=0$. The main inequalities still assume $n\ge2$, as in the manuscript. See [Law](../Parking/Law.lean) and the three [frozen statements](../Parking/Frozen/MainBounds.lean).
3. **Theorem 1.2, profile parameter.** The parameter uses extended nonnegative reals, with the infinite value of the profile explicitly set to one. Finite scale convergence is expressed using `ENNReal.ofReal`. Zero and infinity are both proved. See `Parking.profile` in [Law](../Parking/Law.lean) and [Profile](../Parking/Frozen/Profile.lean).
4. **Proposition 1.3, entropy.** KL divergence uses extended nonnegative reals; the finite real upper bound is embedded with `ENNReal.ofReal`. The full-vector identity also has an exact real-valued companion, so truncation does not hide its meaning. See [Decoupling](../Parking/Frozen/Decoupling.lean) and [EntropyKL](../Parking/EntropyKL.lean).
5. **Marginal estimates and main bounds.** Uniform big-O and comparison assertions are made into explicit existential or numerical bounds. Witnesses precede the full size/index ranges, and joint assertions retain their shared constants. See `Parking.parkingG_marginal` in [MarginalSquares](../Parking/MarginalSquares.lean) and [MainBounds](../Parking/Frozen/MainBounds.lean).
6. **Implicit calculations and cited boundaries.** Omitted calculations, including Borel normalization and the Gaussian expectation, are supplied. The manuscript's endpoint-tail, prefix-product/support, entropy, scalar and characteristic-function routes are consumed by the concluding proofs. Inside a cited theorem, another valid proof of the exact needed specialization is permitted. The separate geometric remark proves actual Euclidean volume and its precise Lorentzian specialization; it is not a definition of volume by the desired polynomial. See [BorelEndpoint](../Parking/BorelEndpoint.lean), [GaussianValue](../Parking/GaussianValue.lean), [SupportNormalization](../Parking/Paper/SupportNormalization.lean), and [PitmanStanleyFormula](../Parking/Paper/PitmanStanleyFormula.lean).

## Scope

The library reconstructs the manuscript's mathematical development, including introductory corollaries and the separate volume remark. The active single Comparator configuration selects exactly `Parking.tvDist_firstCoordsLaw_bounds`, `Parking.tendsto_tvDist_firstCoordsLaw`, and `Parking.klDiv_tvDist_firstCoordsLaw_le`. Historical narrative and AI-use accounts are not mathematical theorem targets. Generalizations of cited articles beyond the interfaces needed by this manuscript are not claimed.

The author approved the export-only migration to Lean 4.35.0 with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Apache-2.0 licensing of the export code including the retained parallel-ledger components, exactly three deliberate Challenge-only placeholders, and the Solution-only imports of the complete frozen proofs. These changes are active in this export. They do not change the three mathematical statements or license the excluded manuscript. The implementation proof-hole count in [formalization.yaml](../formalization.yaml) excludes those three Challenge placeholders, as required by the metadata schema.

The active Lean 4.35.0 export passes its full build, implementation axiom audit and 1570-declaration Lean-kernel replay. The earlier Lean 4.34.0 evidence is retained as history. Private GitHub Actions reports record the actual Comparator and independent-kernel outcomes for the exact commit they check; these are distinct from official Palomar full preflight. The public v1.0.0 release retains its commit-bound successful reports. Official full-preflight, intake and registration outcomes must be read from their separate reports; no independent human mathematical review is claimed. These export and verification statuses are separate from the six mathematical encoding/elaboration entries above.
