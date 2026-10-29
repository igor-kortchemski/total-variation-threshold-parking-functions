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
public import Parking.Law
public import Parking.OccupationCounting
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

/-!
# The disjoint boxes in the Pitman–Stanley volume formula

The cumulative parameter intervals partition the symmetrized order region.
This module proves their volumes and disjointness directly from Lebesgue measure.
The identification with the ordered polytope is a separate geometric obligation.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Parking

/-- A coordinate box indexed by a word, with cumulative parameter cuts. -/
def parkingBox (n : ℕ+) (z : Fin n → ℝ) (a : Fin n → Fin n) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i => Set.Ioc (∑ j ∈ Finset.Iio (a i), z j)
    (∑ j ∈ Finset.Iic (a i), z j)

/-- The union of the boxes indexed by parking words. -/
def parkingBoxUnion (n : ℕ+) (z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  ⋃ a : ParkingFunction n, parkingBox n z a.val

theorem sum_Iic_sub_sum_Iio (n : ℕ+) (z : Fin n → ℝ) (i : Fin n) :
    (∑ j ∈ Finset.Iic i, z j) - (∑ j ∈ Finset.Iio i, z j) = z i := by
  rw [← Finset.Iio_insert, Finset.sum_insert (by simp)]
  ring

theorem measurableSet_parkingBox (n : ℕ+) (z : Fin n → ℝ) (a : Fin n → Fin n) :
    MeasurableSet (parkingBox n z a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- The exact Lebesgue volume of a parking box, including zero-length intervals. -/
theorem volume_parkingBox (n : ℕ+) (z : Fin n → ℝ) (a : Fin n → Fin n) :
    volume (parkingBox n z a) = ∏ i, ENNReal.ofReal (z (a i)) := by
  rw [parkingBox, Real.volume_pi_Ioc]
  simp only [sum_Iic_sub_sum_Iio]

/-- Distinct word boxes are disjoint for all nonnegative parameter vectors. -/
theorem disjoint_parkingBox (n : ℕ+) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    {a b : Fin n → Fin n} (hab : a ≠ b) :
    Disjoint (parkingBox n z a) (parkingBox n z b) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  have step {a b : Fin n → Fin n} {i : Fin n} (hlt : a i < b i) :
      Disjoint (parkingBox n z a) (parkingBox n z b) := by
    apply Set.disjoint_left.mpr
    intro x ha hb
    have hxa := ha i (Set.mem_univ i)
    have hxb := hb i (Set.mem_univ i)
    have hcut : ∑ j ∈ Finset.Iic (a i), z j ≤ ∑ j ∈ Finset.Iio (b i), z j :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => Finset.mem_Iio.mpr ((Finset.mem_Iic.mp hj).trans_lt hlt))
        (fun j _ _ => hz j)
    exact (hxa.2.trans hcut).not_gt hxb.1
  rcases lt_or_gt_of_ne hi with h | h
  · exact step h
  · exact (step h).symm

/-- The box union has exactly the parking-function polynomial as its volume. -/
theorem volume_parkingBoxUnion (n : ℕ+) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    volume (parkingBoxUnion n z) =
      ∑ a : ParkingFunction n, ∏ i, ENNReal.ofReal (z (a.val i)) := by
  rw [parkingBoxUnion, measure_iUnion]
  · rw [tsum_fintype]
    exact Finset.sum_congr rfl fun a _ => volume_parkingBox n z a.val
  · intro a b hab
    exact disjoint_parkingBox n z hz (fun h => hab (Subtype.ext h))
  · exact fun a => measurableSet_parkingBox n z a.val

/-- The real form of the preceding geometric volume identity. -/
theorem volume_parkingBoxUnion_toReal (n : ℕ+) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (volume (parkingBoxUnion n z)).toReal = ∑ a : ParkingFunction n, ∏ i, z (a.val i) := by
  rw [volume_parkingBoxUnion n z hz, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_prod, ENNReal.toReal_ofReal (hz _)]
  · intro a _
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

/-- The occupation polynomial is the parking-word polynomial divided by the
number of parking functions. This is an algebraic probability normalization,
independent of the geometric volume formula. -/
theorem eval_countPoly_eq_parking_sum (n : ℕ+) (z : Fin n → ℝ) :
    MvPolynomial.eval z (countPoly (parkingWordLaw n)) =
      ((((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ) : ℝ)⁻¹ *
        ∑ a : ParkingFunction n, ∏ i, z (a.val i) := by
  classical
  rw [countPoly, map_sum]
  simp only [MvPolynomial.smul_eval, map_prod, MvPolynomial.eval_X,
    parkingWordLaw_real_singleton]
  have hsum : (∑ a : Fin n → Fin n,
      if isParkingFunction a then ∏ i, z (a i) else 0) =
        ∑ a : ParkingFunction n, ∏ i, z (a.val i) := by
    refine (Fintype.sum_of_injective (fun a : ParkingFunction n => a.val)
      Subtype.val_injective _ _ (fun a ha => ?_) (fun a => ?_)).symm
    · have hn : ¬ isParkingFunction a := fun h => ha ⟨⟨a, h⟩, rfl⟩
      simp [hn]
    · simp [a.property]
  rw [← hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

/-- The precise polynomial represented by the volume of the symmetrized boxes.
The remaining Pitman–Stanley volume theorem must identify this union with
`n!` copies, up to null boundaries, of the prefix-inequality polytope. -/
theorem eval_countPoly_eq_volume_parkingBoxUnion (n : ℕ+) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    MvPolynomial.eval z (countPoly (parkingWordLaw n)) =
      ((((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ) : ℝ)⁻¹ *
        (volume (parkingBoxUnion n z)).toReal := by
  rw [volume_parkingBoxUnion_toReal n z hz, eval_countPoly_eq_parking_sum]

end Parking

end
