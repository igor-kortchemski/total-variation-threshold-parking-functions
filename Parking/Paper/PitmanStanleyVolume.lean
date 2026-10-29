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

public import Parking.Paper.PitmanStanley
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Cumulative coordinates for the Pitman–Stanley volume

The actual prefix-inequality polytope is transformed by a determinant-one
linear map into its ordered-coordinate region. These are geometric measures;
no volume is defined to equal the desired occupation polynomial.
-/

@[expose] public section

namespace Parking

open MeasureTheory Finset Function
open scoped ENNReal

/-- The lower-triangular prefix-sum matrix. -/
def pitmanStanleyPrefixMatrix (n : ℕ+) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j ≤ i then 1 else 0

/-- The cumulative-coordinate linear map. -/
noncomputable def pitmanStanleyPrefixSum (n : ℕ+) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLin' (pitmanStanleyPrefixMatrix n)

/-- Its coordinates are exactly the finite prefix sums. -/
theorem pitmanStanleyPrefixSum_apply (n : ℕ+) (y : Fin n → ℝ) (i : Fin n) :
    pitmanStanleyPrefixSum n y i = ∑ j ∈ Iic i, y j := by
  rw [pitmanStanleyPrefixSum, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  simp only [pitmanStanleyPrefixMatrix, ite_mul, one_mul, zero_mul, ← sum_filter]
  congr 1
  ext j
  simp

/-- The diagonal entries are one and the matrix is lower triangular. -/
theorem det_pitmanStanleyPrefixSum (n : ℕ+) :
    LinearMap.det (pitmanStanleyPrefixSum n) = 1 := by
  rw [pitmanStanleyPrefixSum, LinearMap.det_toLin']
  have htri : (pitmanStanleyPrefixMatrix n).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp [pitmanStanleyPrefixMatrix, not_le.mpr hij]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp [pitmanStanleyPrefixMatrix]

/-- The cumulative-coordinate transformation preserves Lebesgue measure. -/
theorem measurePreserving_pitmanStanleyPrefixSum (n : ℕ+) :
    MeasurePreserving (pitmanStanleyPrefixSum n) volume volume := by
  refine ⟨(LinearMap.continuous_on_pi _).measurable, ?_⟩
  have hdet : LinearMap.det (pitmanStanleyPrefixSum n) ≠ 0 := by
    rw [det_pitmanStanleyPrefixSum]
    norm_num
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  simpa only [det_pitmanStanleyPrefixSum, inv_one, abs_one, ENNReal.ofReal_one, one_smul] using h

/-- The ordered chamber after cumulative coordinates. -/
def pitmanStanleyOrderedRegion (n : ℕ+) (z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {s | (∀ i, 0 ≤ s i) ∧ Monotone s ∧ ∀ i, s i ≤ ∑ j ∈ Iic i, z j}

/-- The ordered chamber is closed, including for zero parameters. -/
theorem isClosed_pitmanStanleyOrderedRegion (n : ℕ+) (z : Fin n → ℝ) :
    IsClosed (pitmanStanleyOrderedRegion n z) := by
  change IsClosed ({s : Fin n → ℝ | ∀ i, 0 ≤ s i} ∩
    ({s : Fin n → ℝ | ∀ i j, i ≤ j → s i ≤ s j} ∩
      {s : Fin n → ℝ | ∀ i, s i ≤ ∑ j ∈ Iic i, z j}))
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · apply IsClosed.inter
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le (continuous_apply i) (continuous_apply j)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const

/-- Nonnegative increments are equivalent to nonnegative monotone cumulative coordinates. -/
theorem nonneg_iff_pitmanStanleyPrefixSum (n : ℕ+) (y : Fin n → ℝ) :
    (∀ i, 0 ≤ y i) ↔
      (∀ i, 0 ≤ pitmanStanleyPrefixSum n y i) ∧ Monotone (pitmanStanleyPrefixSum n y) := by
  constructor
  · intro hy
    constructor
    · intro i
      rw [pitmanStanleyPrefixSum_apply]
      exact sum_nonneg fun j _ => hy j
    · intro i j hij
      simp only [pitmanStanleyPrefixSum_apply]
      exact sum_le_sum_of_subset_of_nonneg (Iic_subset_Iic.mpr hij) (fun k _ _ => hy k)
  · rintro ⟨hpos, hmono⟩ i
    have hsum := sum_Iio_add_eq_sum_Iic (f := y) i
    by_cases hi : (i : ℕ) = 0
    · have hIio : Iio i = ∅ := by
        ext j
        simp [Fin.lt_def, hi]
      rw [hIio, sum_empty, zero_add] at hsum
      rw [hsum]
      simpa only [pitmanStanleyPrefixSum_apply] using hpos i
    · let k : Fin n := ⟨(i : ℕ) - 1, by omega⟩
      have hk : k ≤ i := by change (i : ℕ) - 1 ≤ (i : ℕ); omega
      have hIic : Iic k = Iio i := by
        ext j
        simp only [mem_Iic, mem_Iio]
        change (j : ℕ) ≤ (i : ℕ) - 1 ↔ (j : ℕ) < (i : ℕ)
        omega
      have hle := hmono hk
      simp only [pitmanStanleyPrefixSum_apply] at hle
      rw [hIic, ← hsum] at hle
      linarith

/-- The ordered chamber has exactly the original polytope as its preimage. -/
theorem preimage_pitmanStanleyOrderedRegion (n : ℕ+) (z : Fin n → ℝ) :
    pitmanStanleyPrefixSum n ⁻¹' pitmanStanleyOrderedRegion n z = pitmanStanleyPolytope n z := by
  ext y
  change ((∀ i, 0 ≤ pitmanStanleyPrefixSum n y i) ∧ Monotone (pitmanStanleyPrefixSum n y) ∧
    ∀ i, pitmanStanleyPrefixSum n y i ≤ ∑ j ∈ Iic i, z j) ↔
    ((∀ i, 0 ≤ y i) ∧ ∀ i, ∑ j ∈ Iic i, y j ≤ ∑ j ∈ Iic i, z j)
  rw [← and_assoc, ← nonneg_iff_pitmanStanleyPrefixSum]
  simp only [pitmanStanleyPrefixSum_apply]

/-- The geometric polytope and its ordered chamber have the same Lebesgue volume. -/
theorem volume_pitmanStanleyPolytope_eq_orderedRegion (n : ℕ+) (z : Fin n → ℝ) :
    volume (pitmanStanleyPolytope n z) = volume (pitmanStanleyOrderedRegion n z) := by
  rw [← preimage_pitmanStanleyOrderedRegion]
  exact (measurePreserving_pitmanStanleyPrefixSum n).measure_preimage
    (isClosed_pitmanStanleyOrderedRegion n z).measurableSet.nullMeasurableSet

/-- The chamber indexed by a coordinate permutation. -/
def pitmanStanleyPermutedRegion (n : ℕ+) (z : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  (fun x => x ∘ σ) ⁻¹' pitmanStanleyOrderedRegion n z

/-- The union of all coordinate orderings of the ordered region. -/
def pitmanStanleySymmetrizedRegion (n : ℕ+) (z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  ⋃ σ : Equiv.Perm (Fin n), pitmanStanleyPermutedRegion n z σ

/-- Membership exposes the precise permutation and ordered-coordinate conditions. -/
theorem mem_pitmanStanleySymmetrizedRegion_iff (n : ℕ+) (z x : Fin n → ℝ) :
    x ∈ pitmanStanleySymmetrizedRegion n z ↔
      ∃ σ : Equiv.Perm (Fin n), x ∘ σ ∈ pitmanStanleyOrderedRegion n z := by
  simp only [pitmanStanleySymmetrizedRegion, Set.mem_iUnion, pitmanStanleyPermutedRegion,
    Set.mem_preimage]

/-- The canonical sorted tuple identifies membership in the symmetric union. -/
theorem mem_pitmanStanleySymmetrizedRegion_iff_sorted (n : ℕ+) (z x : Fin n → ℝ) :
    x ∈ pitmanStanleySymmetrizedRegion n z ↔
      (x ∘ Tuple.sort x) ∈ pitmanStanleyOrderedRegion n z := by
  rw [mem_pitmanStanleySymmetrizedRegion_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    have heq := Tuple.unique_monotone hσ.2.1 (Tuple.monotone_sort x)
    rwa [heq] at hσ
  · intro hx
    exact ⟨Tuple.sort x, hx⟩

/-- Coordinate permutations preserve the product Lebesgue measure. -/
theorem measurePreserving_comp_perm (n : ℕ+) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → ℝ => x ∘ σ) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  convert h using 1
  funext x i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- Every permuted chamber is measurable. -/
theorem measurableSet_pitmanStanleyPermutedRegion (n : ℕ+) (z : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : MeasurableSet (pitmanStanleyPermutedRegion n z σ) :=
  (isClosed_pitmanStanleyOrderedRegion n z).measurableSet.preimage
    (measurePreserving_comp_perm n σ).measurable

/-- All permuted chambers have the same geometric volume. -/
theorem volume_pitmanStanleyPermutedRegion (n : ℕ+) (z : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    volume (pitmanStanleyPermutedRegion n z σ) = volume (pitmanStanleyOrderedRegion n z) :=
  (measurePreserving_comp_perm n σ).measure_preimage
    (isClosed_pitmanStanleyOrderedRegion n z).measurableSet.nullMeasurableSet

/-- Coincident distinct coordinates form a null hyperplane. -/
theorem volume_coordinate_eq_zero (n : ℕ+) {i j : Fin n} (hij : i ≠ j) :
    volume {x : Fin n → ℝ | x i = x j} = 0 := by
  classical
  let S : Submodule ℝ (Fin n → ℝ) :=
    LinearMap.ker ((LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j)
  have hS : S ≠ ⊤ := by
    intro htop
    have hx : Pi.single i (1 : ℝ) ∈ S := by rw [htop]; trivial
    simp [S, LinearMap.mem_ker, hij.symm] at hx
  have heq : (S : Set (Fin n → ℝ)) = {x | x i = x j} := by
    ext x
    simp [S, LinearMap.mem_ker, sub_eq_zero]
  rw [← heq]
  exact Measure.addHaar_submodule volume S hS

/-- Two distinct permutation chambers overlap only on a null coincidence hyperplane. -/
theorem aedisjoint_pitmanStanleyPermutedRegion (n : ℕ+) (z : Fin n → ℝ) :
    Pairwise (MeasureTheory.AEDisjoint volume on pitmanStanleyPermutedRegion n z) := by
  classical
  intro σ τ hστ
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    by_contra h
    push Not at h
    exact hστ (Equiv.ext h)
  change volume (pitmanStanleyPermutedRegion n z σ ∩ pitmanStanleyPermutedRegion n z τ) = 0
  refine measure_mono_null ?_ (volume_coordinate_eq_zero n hi)
  intro x hx
  have hσ : Monotone (x ∘ σ) := hx.1.2.1
  have hτ : Monotone (x ∘ τ) := hx.2.2.1
  exact congr_fun (Tuple.unique_monotone hσ hτ) i

/-- Symmetrizing the ordered chamber multiplies the polytope volume by `n!`.
The equality includes degenerate parameters: null boundaries are handled by
a.e. disjointness, not by assuming strict positivity of the coordinates. -/
theorem volume_pitmanStanleySymmetrizedRegion (n : ℕ+) (z : Fin n → ℝ) :
    volume (pitmanStanleySymmetrizedRegion n z) =
      ((Nat.factorial (n : ℕ) : ℕ) : ℝ≥0∞) * volume (pitmanStanleyPolytope n z) := by
  rw [pitmanStanleySymmetrizedRegion,
    measure_iUnion₀ (aedisjoint_pitmanStanleyPermutedRegion n z)
      (fun σ => (measurableSet_pitmanStanleyPermutedRegion n z σ).nullMeasurableSet)]
  simp only [volume_pitmanStanleyPermutedRegion, tsum_fintype, sum_const, card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [volume_pitmanStanleyPolytope_eq_orderedRegion]

end Parking
end
