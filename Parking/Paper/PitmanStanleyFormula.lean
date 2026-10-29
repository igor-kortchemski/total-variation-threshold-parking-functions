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

public import Parking.Paper.ParkingBoxOrder
public import Parking.Paper.PitmanStanleyVolume
public import Parking.Paper.Lorentzian

/-!
# The Pitman–Stanley volume-polynomial remark

The geometric volume formula is obtained by determinant-one cumulative
coordinates and a.e.-disjoint permutation chambers. The volume-Lorentzian
result is specialized to the actual suffix simplices, with a proved geometric
volume characterization. Its internal combinatorial proof uses the normalized
M-convex support theorem, never a final parking log-concavity result.
-/

public section

open MeasureTheory MvPolynomial
open scoped ENNReal

namespace Parking

/-- A coordinate-zero hyperplane is Lebesgue-null. -/
theorem volume_coordinate_zero (n : ℕ+) (i : Fin n) :
    volume {x : Fin n → ℝ | x i = 0} = 0 := by
  classical
  let S : Submodule ℝ (Fin n → ℝ) := LinearMap.ker (LinearMap.proj i)
  have hS : S ≠ ⊤ := by
    intro htop
    have hx : Pi.single i (1 : ℝ) ∈ S := by rw [htop]; trivial
    simp [S, LinearMap.mem_ker] at hx
  have heq : (S : Set (Fin n → ℝ)) = {x | x i = 0} := by
    ext x
    simp [S, LinearMap.mem_ker]
  rw [← heq]
  exact Measure.addHaar_submodule volume S hS

/-- Parking boxes and the symmetrized ordered chamber differ only on coordinate-zero faces. -/
theorem parkingBoxUnion_ae_eq_symmetrizedRegion (n : ℕ+) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    parkingBoxUnion n z =ᵐ[volume] pitmanStanleySymmetrizedRegion n z := by
  have hnonzero : ∀ᵐ x : Fin n → ℝ ∂volume, ∀ i, x i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    apply ae_iff.mpr
    simpa only [not_not] using volume_coordinate_zero n i
  filter_upwards [hnonzero] with x hx
  apply propext
  rw [mem_parkingBoxUnion_iff_sorted n z hz, mem_pitmanStanleySymmetrizedRegion_iff_sorted]
  change ((∀ i, 0 < x i) ∧ ∀ i, x (Tuple.sort x i) ≤ ∑ j ∈ Finset.Iic i, z j) ↔
    ((∀ i, 0 ≤ x (Tuple.sort x i)) ∧ Monotone (x ∘ Tuple.sort x) ∧
      ∀ i, x (Tuple.sort x i) ≤ ∑ j ∈ Finset.Iic i, z j)
  constructor
  · rintro ⟨hp, hb⟩
    exact ⟨fun i => (hp _).le, Tuple.monotone_sort x, hb⟩
  · rintro ⟨hp, _, hb⟩
    refine ⟨fun i => ?_, hb⟩
    have hi : 0 ≤ x i := by simpa only [Equiv.apply_symm_apply] using hp ((Tuple.sort x).symm i)
    exact lt_of_le_of_ne hi (Ne.symm (hx i))

/-- PS02 Theorem 11: the actual polytope volume is the parking-word polynomial divided by `n!`. -/
theorem factorial_mul_volume_pitmanStanley (n : ℕ+) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    ((n : ℕ).factorial : ℝ) * (volume (pitmanStanleyPolytope n z)).toReal =
      ∑ a : ParkingFunction n, ∏ i, z (a.val i) := by
  have h := congrArg ENNReal.toReal
    ((measure_congr (parkingBoxUnion_ae_eq_symmetrizedRegion n z hz)).trans
      (volume_pitmanStanleySymmetrizedRegion n z))
  rw [volume_parkingBoxUnion_toReal n z hz, ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  exact h.symm

/-- The occupation polynomial is the geometric volume polynomial times the precise positive scalar. -/
theorem eval_countPoly_eq_volume_pitmanStanley (n : ℕ+) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    eval z (countPoly (parkingWordLaw n)) =
      (((n : ℕ).factorial : ℝ) / ((((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ) : ℝ)) *
        (volume (pitmanStanleyPolytope n z)).toReal := by
  rw [eval_countPoly_eq_parking_sum, ← factorial_mul_volume_pitmanStanley n z hz]
  ring

/-- The factorial-normalized support polynomial has the genuine geometric volume characterization. -/
theorem eval_supportGenFun_eq_volume_pitmanStanley (n : ℕ+) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    eval z (supportGenFun (parkingCountSet n)) =
      (volume (pitmanStanleyPolytope n z)).toReal := by
  have h := eval_countPoly_eq_volume_pitmanStanley n z hz
  rw [countPoly_parkingWordLaw, smul_eval] at h
  exact mul_left_cancel₀ (by positivity :
    (((n : ℕ).factorial : ℝ) / ((((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ) : ℝ)) ≠ 0) h

/-- The exact suffix-simplex specialization of BH20 Theorem 4.1 needed by the
remark. The first component proves that the displayed polynomial really is the
Minkowski-volume polynomial, including degenerate nonnegative parameters.
The Lorentzian proof uses independent M-convex support theory and no final
occupation log-concavity theorem. -/
theorem pitmanStanley_volume_polynomial_lorentzian (n : ℕ+) :
    (∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) →
      eval z (supportGenFun (parkingCountSet n)) =
        (volume (pitmanStanleyMinkowskiSum n z)).toReal) ∧
      Lorentzian (n : ℕ) (supportGenFun (parkingCountSet n)) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [← pitmanStanleyPolytope_eq_minkowskiSum n z hz]
    exact eval_supportGenFun_eq_volume_pitmanStanley n z hz
  · exact lorentzian_supportGenFun (parkingCountSet n)
      (fun _ h => degree_of_mem_parkingCountSet h) (isMConvex_parkingCountSet n)

/-- The manuscript's separate Pitman–Stanley remark, with one positive scalar
and with its volume-Lorentzian route explicitly consumed. -/
theorem pitmanStanley_occupation_remark (n : ℕ+) :
    ∃ c : ℝ, 0 < c ∧
      (∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) →
        eval z (countPoly (parkingWordLaw n)) =
          c * (volume (pitmanStanleyPolytope n z)).toReal) ∧
      Lorentzian (n : ℕ) (countPoly (parkingWordLaw n)) := by
  obtain ⟨hvolume, hlor⟩ := pitmanStanley_volume_polynomial_lorentzian n
  let c : ℝ := ((n : ℕ).factorial : ℝ) /
    ((((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ) : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_, ?_⟩
  · intro z hz
    rw [countPoly_parkingWordLaw, smul_eval, hvolume z hz,
      ← pitmanStanleyPolytope_eq_minkowskiSum n z hz]
  · rw [countPoly_parkingWordLaw]
    exact hlor.smul hc

end Parking

end
