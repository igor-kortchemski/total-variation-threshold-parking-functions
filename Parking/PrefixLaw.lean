/-
Copyright (c) 2026 Igor Kortchemski.
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Parking.CountPoly
public import Parking.Exchangeable
public import Parking.External
public import Parking.Paper.Lorentzian
import Parking.Occupation
import Parking.WordLaw
import Mathlib.GroupTheory.Perm.Fin

/-!
# Count-generating polynomials of initial segments of exchangeable laws

The proofs of `lem:occupation_logconcavity` and `lem:sample_entropy` apply
[LS26, Lemma 3.4(1)] repeatedly: the laws of the initial segments of an exchangeable law whose
count-generating polynomial is strongly log-concave again have strongly log-concave
count-generating polynomials. The source route converts strong log-concavity to
the genuine Lorentzian property, then repeatedly uses its directional-derivative closure.

* `isHomogeneous_countPoly`: `h_μ` is homogeneous of degree `m` for a law `μ` on `[d]^m`.
* `countPoly_coordLaw_succ`: for an exchangeable finite law `μ` on `[d]^{m+1}`, deleting the
  last coordinate gives a law with count-generating polynomial
  `(1 / (m + 1)) ∑_a ∂_a h_μ` ([LS26, identity (3.3)]). Indeed
  `∂_a ∏_j x_{ω_j} = ∑_{j : ω_j = a} ∏_{i ≠ j} x_{ω_i}`, and by exchangeability the law of `ω`
  with coordinate `j` deleted does not depend on `j`.
* `lorentzian_countPoly_coordLaw`: algebraic Lorentzianity of `h_μ` passes to every
  initial segment by downward induction and `Lorentzian.dirDeriv`.
* `stronglyLogConcave_countPoly_coordLaw`: the source strong-hypothesis interface, using
  the proved homogeneous strong/Lorentzian equivalence.
* `completelyLogConcave_countPoly_coordLaw`: the independently useful complete variant.
* `completelyLogConcave_countPoly_firstCoordsLaw`: conditional on the citation interface
  `BH20.SupportGenFunCLC`, the count-generating polynomial of `P_{n,k}` is completely
  log-concave.

The parking-law consequences use the citation interface `BH20.SupportGenFunCLC`;
the general closure lemmas do not assume it.
-/

public section

open MeasureTheory MvPolynomial

namespace Parking

/-! ### Homogeneity -/

/-- The count-generating polynomial of a law on `[d]^m` is homogeneous of degree `m`. -/
theorem isHomogeneous_countPoly {m d : ℕ} (μ : Measure (Fin m → Fin d)) :
    (countPoly μ).IsHomogeneous m := by
  refine IsHomogeneous.sum _ _ _ fun ω _ => ?_
  rw [smul_eq_C_mul]
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin m)) (fun j => (X (ω j) :
    MvPolynomial (Fin d) ℝ)) (fun _ => 1) fun j _ => isHomogeneous_X ℝ (ω j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  exact h.C_mul _

/-! ### Coordinate laws -/

/-- The law of the first `k` coordinates of a finite law is finite. -/
instance isFiniteMeasure_coordLaw {N d : ℕ} (μ : Measure (Fin N → Fin d)) [IsFiniteMeasure μ]
    {k : ℕ} (hk : k ≤ N) : IsFiniteMeasure (coordLaw μ hk) := by
  unfold coordLaw
  infer_instance

/-- Keeping all `N` coordinates of a law on `[d]^N` gives the law itself. -/
theorem coordLaw_self {N d : ℕ} (μ : Measure (Fin N → Fin d)) (h : N ≤ N) :
    coordLaw μ h = μ :=
  Measure.map_id

/-- Keeping the first `l` coordinates, then the first `k ≤ l` of those, amounts to keeping
the first `k` coordinates. -/
theorem coordLaw_coordLaw {N d : ℕ} (μ : Measure (Fin N → Fin d)) {k l : ℕ} (hkl : k ≤ l)
    (hl : l ≤ N) : coordLaw (coordLaw μ hl) hkl = coordLaw μ (hkl.trans hl) := by
  rw [coordLaw, coordLaw, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

/-- The count-generating polynomial of an image law: for a finite law `μ` on `[d]^m` and a
map `f : [d]^m → [d]^k`, `h_{f_* μ}(x) = ∑_ω μ(ω) ∏_i x_{f(ω)_i}`. -/
theorem countPoly_map {m k d : ℕ} (μ : Measure (Fin m → Fin d)) [IsFiniteMeasure μ]
    (f : (Fin m → Fin d) → Fin k → Fin d) :
    countPoly (μ.map f) = ∑ ω, μ.real {ω} • ∏ i, X (f ω i) := by
  classical
  have h : ∀ η, (μ.map f).real {η} = ∑ ω, if f ω = η then μ.real {ω} else 0 := by
    intro η
    rw [map_measureReal_apply (measurable_of_finite f) (measurableSet_singleton η),
      ← Finset.sum_filter, sum_measureReal_singleton]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Finset.mem_univ,
      true_and, Set.mem_ofPred_eq]
  simp only [countPoly, h, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]

/-- For an exchangeable law on `[d]^{m+1}`, the law of the word with coordinate `j` deleted
(the remaining coordinates kept in increasing order) is the law of the word with its first
coordinate deleted. Indeed, the permutation `j.cycleRange⁻¹` sends `0` to `j` and
`1, …, m`, in increasing order, to the other coordinates. -/
theorem IsExchangeableLaw.map_succAbove {m d : ℕ} {μ : Measure (Fin (m + 1) → Fin d)}
    (hμ : IsExchangeableLaw μ) (j : Fin (m + 1)) :
    μ.map (fun ω i => ω (j.succAbove i)) = μ.map (fun ω i => ω i.succ) := by
  calc μ.map (fun ω i => ω (j.succAbove i))
      = μ.map ((fun ω i => ω i.succ) ∘ fun ω i => ω (j.cycleRange.symm i)) := by
        congr 1
        funext ω i
        simp only [Function.comp_apply, Fin.cycleRange_symm_succ]
    _ = (μ.map fun ω i => ω (j.cycleRange.symm i)).map (fun ω i => ω i.succ) :=
        (Measure.map_map (measurable_of_finite _) (measurable_of_finite _)).symm
    _ = μ.map (fun ω i => ω i.succ) := by rw [hμ j.cycleRange.symm]

/-- For an exchangeable law on `[d]^{m+1}`, the law of the word with coordinate `j` deleted
(the remaining coordinates kept in increasing order) is the law of its first `m`
coordinates. -/
theorem IsExchangeableLaw.map_succAbove_eq_coordLaw {m d : ℕ}
    {μ : Measure (Fin (m + 1) → Fin d)} (hμ : IsExchangeableLaw μ) (j : Fin (m + 1)) :
    μ.map (fun ω i => ω (j.succAbove i)) = Parking.coordLaw μ (Nat.le_succ m) := by
  rw [hμ.map_succAbove j, ← hμ.map_succAbove (Fin.last m), Parking.coordLaw]
  congr 1
  funext ω i
  rw [Fin.succAbove_last]
  rfl

/-! ### The identity `h_{coordLaw μ} = (1 / (m + 1)) ∑_a ∂_a h_μ` -/

/-- `∑_a ∂_a x_b = 1`. -/
theorem sum_pderiv_X {d : ℕ} (b : Fin d) :
    ∑ a, pderiv a (X b : MvPolynomial (Fin d) ℝ) = 1 := by
  rw [Finset.sum_eq_single b (fun a _ hab => pderiv_X_of_ne (Ne.symm hab))
    (fun h => absurd (Finset.mem_univ b) h), pderiv_X_self]

/-- `∑_a ∂_a ∏_{j ≤ m+1} x_{ω_j} = ∑_j ∏_{i ≠ j} x_{ω_i}`, the coordinates other than `j`
being listed as `j.succAbove i` for `i : Fin m`. -/
theorem sum_pderiv_prod_X {m d : ℕ} (ω : Fin (m + 1) → Fin d) :
    ∑ a, pderiv a (∏ j, X (ω j) : MvPolynomial (Fin d) ℝ) =
      ∑ j : Fin (m + 1), ∏ i : Fin m, X (ω (j.succAbove i)) := by
  induction m with
  | zero => rw [Fin.prod_univ_one, sum_pderiv_X, Fin.sum_univ_one, Fin.prod_univ_zero]
  | succ m ih =>
    rw [Fin.prod_univ_succ]
    simp only [pderiv_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      sum_pderiv_X, one_mul, ih fun j => ω j.succ]
    rw [Fin.sum_univ_succ (f := fun j : Fin (m + 2) => ∏ i : Fin (m + 1), X (ω (j.succAbove i)))]
    simp only [Fin.zero_succAbove, Fin.prod_univ_succ (n := m), Fin.succ_succAbove_zero,
      Fin.succ_succAbove_succ, Finset.mul_sum]

/-- [LS26, Lemma 3.4(1), identity (3.3)]: for an exchangeable finite law `μ` on `[d]^{m+1}`,
the law of the first `m` coordinates has count-generating polynomial
`(1 / (m + 1)) ∑_a ∂_a h_μ`, the derivative of `h_μ` in the constant direction
`(1 / (m + 1), …, 1 / (m + 1))`. -/
theorem countPoly_coordLaw_succ {m d : ℕ} (μ : Measure (Fin (m + 1) → Fin d))
    [IsFiniteMeasure μ] (hμ : IsExchangeableLaw μ) :
    countPoly (coordLaw μ (Nat.le_succ m)) =
      dirDeriv (fun _ => ((m : ℝ) + 1)⁻¹) (countPoly μ) := by
  have key : ∑ a, pderiv a (countPoly μ) =
      ((m : ℝ) + 1) • countPoly (coordLaw μ (Nat.le_succ m)) := by
    calc ∑ a, pderiv a (countPoly μ)
        = ∑ ω, μ.real {ω} • ∑ a, pderiv a (∏ j, X (ω j) : MvPolynomial (Fin d) ℝ) := by
          simp only [countPoly, map_sum, Derivation.map_smul, Finset.smul_sum]
          exact Finset.sum_comm
      _ = ∑ ω, μ.real {ω} • ∑ j : Fin (m + 1), ∏ i : Fin m, X (ω (j.succAbove i)) := by
          simp only [sum_pderiv_prod_X]
      _ = ∑ j : Fin (m + 1), countPoly (μ.map fun ω i => ω (j.succAbove i)) := by
          simp only [countPoly_map, Finset.smul_sum]
          exact Finset.sum_comm
      _ = ∑ _j : Fin (m + 1), countPoly (coordLaw μ (Nat.le_succ m)) := by
          simp only [hμ.map_succAbove_eq_coordLaw]
      _ = ((m : ℝ) + 1) • countPoly (coordLaw μ (Nat.le_succ m)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
            Nat.cast_succ]
  rw [dirDeriv_apply, ← Finset.smul_sum, key, smul_smul, inv_mul_cancel₀ (by positivity),
    one_smul]

/-! ### Complete log-concavity of initial segments -/

/-- [LS26, Lemma 3.4(1)], applied repeatedly (`lem:occupation_logconcavity`): if a finite exchangeable law on `[d]^N` has a completely log-concave
count-generating polynomial, so does the law of its first `k` coordinates, for every
`k ≤ N`. -/
theorem completelyLogConcave_countPoly_coordLaw {N d : ℕ} (μ : Measure (Fin N → Fin d))
    [IsFiniteMeasure μ] (hμ : IsExchangeableLaw μ) (h : CompletelyLogConcave (countPoly μ))
    {k : ℕ} (hk : k ≤ N) : CompletelyLogConcave (countPoly (coordLaw μ hk)) := by
  induction hk using Nat.decreasingInduction with
  | self => rwa [coordLaw_self]
  | of_succ k hk ih =>
    rw [← coordLaw_coordLaw μ (Nat.le_succ k) hk,
      countPoly_coordLaw_succ _ (IsExchangeableLaw.coordLaw μ hμ hk)]
    exact ih.dirDeriv fun _ => by positivity

/-- [LS26, Lemma 3.4(1)] in its algebraic Lorentzian form. Each deletion is
literally the positive all-ones directional derivative, and the induction
consumes the proved Lorentzian derivative closure. -/
theorem lorentzian_countPoly_coordLaw {N d : ℕ} (μ : Measure (Fin N → Fin d))
    [IsFiniteMeasure μ] (hμ : IsExchangeableLaw μ) (h : Lorentzian N (countPoly μ))
    {k : ℕ} (hk : k ≤ N) : Lorentzian k (countPoly (coordLaw μ hk)) := by
  induction hk using Nat.decreasingInduction with
  | self => rwa [coordLaw_self]
  | of_succ k hk ih =>
    rw [← coordLaw_coordLaw μ (Nat.le_succ k) hk,
      countPoly_coordLaw_succ _ (IsExchangeableLaw.coordLaw μ hμ hk)]
    simpa using ih.dirDeriv (fun _ => by positivity)

/-- [LS26, Lemma 3.4(1)] in the manuscript's strong-log-concavity form.
Homogeneity of the count polynomial permits the proved strong/complete equivalence;
the deletion derivative identity then gives every initial segment. -/
theorem stronglyLogConcave_countPoly_coordLaw {N d : ℕ} (μ : Measure (Fin N → Fin d))
    [IsFiniteMeasure μ] (hμ : IsExchangeableLaw μ) (h : StronglyLogConcave (countPoly μ))
    {k : ℕ} (hk : k ≤ N) : StronglyLogConcave (countPoly (coordLaw μ hk)) :=
  (lorentzian_countPoly_coordLaw μ hμ
    (h.lorentzian (isHomogeneous_countPoly μ)) hk).stronglyLogConcave

/-- Conditional on the citation interface `BH20.SupportGenFunCLC`, the
count-generating polynomial `E_n[∏_{r ≤ k} z_{π_n(r)}]` of the law `P_{n,k}` of the first `k`
coordinates of a uniform parking function is completely log-concave
(`lem:occupation_logconcavity`). -/
theorem completelyLogConcave_countPoly_firstCoordsLaw (hBH : BH20.SupportGenFunCLC)
    (n : ℕ+) (k : ℕ) (hk : k ≤ n) :
    CompletelyLogConcave (countPoly (firstCoordsLaw n k hk : Measure (Fin k → Fin n))) := by
  have : IsFiniteMeasure (parkingWordLaw n) := by
    unfold parkingWordLaw
    infer_instance
  rw [firstCoordsLaw_eq_coordLaw]
  exact completelyLogConcave_countPoly_coordLaw _ (isExchangeableLaw_parkingWordLaw n)
    (completelyLogConcave_countPoly_parkingWordLaw hBH n) hk

/-- The source transition: the full occupation polynomial is strongly
log-concave, hence Lorentzian, and Lorentzianity passes to the prefix law. -/
theorem lorentzian_countPoly_firstCoordsLaw (hBH : BH20.SupportGenFunCLC)
    (n : ℕ+) (k : ℕ) (hk : k ≤ n) :
    Lorentzian k (countPoly (firstCoordsLaw n k hk : Measure (Fin k → Fin n))) := by
  have : IsFiniteMeasure (parkingWordLaw n) := by
    unfold parkingWordLaw
    infer_instance
  rw [firstCoordsLaw_eq_coordLaw]
  exact lorentzian_countPoly_coordLaw _ (isExchangeableLaw_parkingWordLaw n)
    ((stronglyLogConcave_countPoly_parkingWordLaw hBH n).lorentzian
      (isHomogeneous_countPoly (parkingWordLaw n))) hk

/-- The strong-log-concavity interface for the prefix law used by the source
product-moment proof, conditional only on the support-generating-function provider. -/
theorem stronglyLogConcave_countPoly_firstCoordsLaw (hBH : BH20.SupportGenFunCLC)
    (n : ℕ+) (k : ℕ) (hk : k ≤ n) :
    StronglyLogConcave (countPoly (firstCoordsLaw n k hk : Measure (Fin k → Fin n))) :=
  (lorentzian_countPoly_firstCoordsLaw hBH n k hk).stronglyLogConcave

end Parking

end
