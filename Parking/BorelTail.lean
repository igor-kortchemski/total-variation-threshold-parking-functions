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

public import Parking.BorelEndpoint

/-!
# Infinite Borel tails and the source marginal expansion

Uniform estimates for the infinite tails in `lem:marginal`. Integer
interval comparisons are passed to the limit using the proved Borel sum.
-/

public section

namespace Parking

open Finset Filter Topology

/-- The positive Borel tail is summable from any positive index. -/
theorem summable_borelWeight_add {j : ℕ} (hj : 1 ≤ j) :
    Summable (fun i => borelWeight (i + j)) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff k).2 hasSum_borelWeight_succ.summable

/-- Explicit two-sided tail bounds obtained from Stirling and interval sums. -/
theorem borelTail_bounds {j : ℕ} (hj : 1 ≤ j) :
    2 / (√(2 * Real.pi) * √(j : ℝ)) -
        1 / (6 * √(2 * Real.pi) * (j : ℝ) * √(j : ℝ)) ≤
      (∑' i, borelWeight (i + j)) ∧
    (∑' i, borelWeight (i + j)) ≤
      2 / (√(2 * Real.pi) * √(j : ℝ)) +
        1 / (√(2 * Real.pi) * (j : ℝ) * √(j : ℝ)) := by
  let P : ℝ := 1 / √(2 * Real.pi)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hshift (m : ℕ) (f : ℕ → ℝ) :
      ∑ i ∈ range m, f (i + j) = ∑ i ∈ Ico j (m + j), f i := by
    rw [range_eq_Ico, sum_Ico_add' f 0 m j, zero_add]
  have hu (m : ℕ) : (∑ i ∈ range m, borelWeight (i + j)) ≤
      P * (1 / ((j : ℝ) * √(j : ℝ)) + 2 / √(j : ℝ)) := by
    rw [hshift]
    calc _ ≤ ∑ i ∈ Ico j (m + j), P * (1 / ((i : ℝ) * √(i : ℝ))) := by
          refine sum_le_sum fun i hi => ?_
          have hi0 : i ≠ 0 := by have := (mem_Ico.1 hi).1; omega
          simpa only [P, one_div_mul_one_div, mul_assoc] using borelWeight_le hi0
      _ = P * ∑ i ∈ Ico j (m + j), 1 / ((i : ℝ) * √(i : ℝ)) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_mul_sqrt_le hj (m + j)) hP
  have hl (m : ℕ) : P * (2 / √(j : ℝ) - 2 / √((m + j : ℕ) : ℝ)) -
      P / 6 * (1 / ((j : ℝ) * √(j : ℝ))) ≤ ∑ i ∈ range m, borelWeight (i + j) := by
    rw [hshift]
    have herr : (∑ i ∈ Ico j (m + j),
        (P * (1 / ((i : ℝ) * √(i : ℝ))) - borelWeight i)) ≤
        P / 6 * (1 / ((j : ℝ) * √(j : ℝ))) := by
      calc _ ≤ ∑ i ∈ Ico j (m + j), P / 12 * (1 / ((i : ℝ) ^ 2 * √(i : ℝ))) := by
            refine sum_le_sum fun i hi => ?_
            have hi0 : i ≠ 0 := by have := (mem_Ico.1 hi).1; omega
            convert sub_borelWeight_le hi0 using 1 <;> dsimp [P] <;> ring
        _ = P / 12 * ∑ i ∈ Ico j (m + j), 1 / ((i : ℝ) ^ 2 * √(i : ℝ)) :=
          (mul_sum _ _ _).symm
        _ ≤ P / 12 * (2 / ((j : ℝ) * √(j : ℝ))) :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_mul_sqrt_le hj (m + j)) (by positivity)
        _ = _ := by ring
    rw [sum_sub_distrib, ← mul_sum] at herr
    have hmain := mul_le_mul_of_nonneg_left
      (sub_le_sum_inv_mul_sqrt hj (show j ≤ m + j by omega)) hP
    linarith
  have htail := (summable_borelWeight_add hj).hasSum.tendsto_sum_nat
  have hz : Tendsto (fun m : ℕ => 2 / √((m + j : ℕ) : ℝ)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat j))
  constructor
  · have hlim : Tendsto (fun m : ℕ => P * (2 / √(j : ℝ) - 2 / √((m + j : ℕ) : ℝ)) -
        P / 6 * (1 / ((j : ℝ) * √(j : ℝ)))) atTop
        (𝓝 (P * (2 / √(j : ℝ)) - P / 6 * (1 / ((j : ℝ) * √(j : ℝ))))) := by
      simpa only [sub_zero] using ((tendsto_const_nhds.sub hz).const_mul P).sub_const
        (P / 6 * (1 / ((j : ℝ) * √(j : ℝ))))
    convert le_of_tendsto_of_tendsto hlim htail (Eventually.of_forall hl) using 1
    dsimp [P]
    ring
  · convert le_of_tendsto' htail hu using 1
    dsimp [P]
    ring

/-- The infinite Borel tail is uniformly comparable to `j⁻¹ᐟ²`, as used
when choosing the manuscript's small absolute endpoint fraction. -/
theorem borelTail_comparable {j : ℕ} (hj : 1 ≤ j) :
    1 / (2 * √(j : ℝ)) ≤ (∑' i, borelWeight (i + j)) ∧
      (∑' i, borelWeight (i + j)) ≤ 2 / √(j : ℝ) := by
  obtain ⟨hl, hu⟩ := borelTail_bounds hj
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hs : 0 < √(j : ℝ) := by positivity
  have hS : 0 < √(2 * Real.pi) := by positivity
  have hSlo : (2 : ℝ) ≤ √(2 * Real.pi) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith [Real.two_le_pi]
  have hShi : √(2 * Real.pi) ≤ 3 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [Real.pi_le_four]
  constructor
  · refine le_trans ?_ hl
    field_simp
    nlinarith
  · refine hu.trans ?_
    field_simp
    nlinarith

/-- Uniform infinite-tail expansion; the coefficient `2 / √(2π)` is `√(2/π)`. -/
theorem abs_borelTail_sub_le {j : ℕ} (hj : 1 ≤ j) :
    |(∑' i, borelWeight (i + j)) - 2 / (√(2 * Real.pi) * √(j : ℝ))| ≤
      1 / (2 * (j : ℝ) * √(j : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := borelTail_bounds hj
  have hS : (2 : ℝ) ≤ √(2 * Real.pi) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith [Real.two_le_pi]
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have h1 : 1 / (√(2 * Real.pi) * (j : ℝ) * √(j : ℝ)) ≤
      1 / (2 * (j : ℝ) * √(j : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have h2 : 1 / (6 * √(2 * Real.pi) * (j : ℝ) * √(j : ℝ)) ≤
      1 / (2 * (j : ℝ) * √(j : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- Uniform source expansion on `1 ≤ j ≤ (n+2)/2` in one-based notation. -/
theorem abs_parkingG_sub_borel_leading_le (n : ℕ+) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ)) :
    |parkingG n j - 2 / (√(2 * Real.pi) * √((j : ℝ) + 1))| ≤
      1 / (2 * ((j : ℝ) + 1) * √((j : ℝ) + 1)) +
      6 * √((j : ℝ) + 1) / ((n : ℝ) + 1) := by
  have ht := abs_parkingG_sub_borelTail_le n j (by omega)
  have hq := abs_borelTail_sub_le (j := (j : ℕ) + 1) (by omega)
  push_cast at hq
  simp only [Nat.add_assoc] at ht
  calc _ ≤ |parkingG n j - ∑' i, borelWeight (i + ((j : ℕ) + 1))| +
      |(∑' i, borelWeight (i + ((j : ℕ) + 1))) -
        2 / (√(2 * Real.pi) * √((j : ℝ) + 1))| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- The absolute left-half bound, now derived from the endpoint/tail expansion. -/
theorem abs_parkingG_le_from_borelTail (n : ℕ+) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ)) :
    |parkingG n j| ≤ 7 / √((j : ℝ) + 1) := by
  have he := abs_parkingG_sub_borel_leading_le n j hj
  have ha : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    nlinarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ (j : ℝ))]
  have hs : (0 : ℝ) < √((j : ℝ) + 1) := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hS : (2 : ℝ) ≤ √(2 * Real.pi) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith [Real.two_le_pi]
  have hm : 2 / (√(2 * Real.pi) * √((j : ℝ) + 1)) ≤ 1 / √((j : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) hs]
    nlinarith
  have hlocal : 1 / (2 * ((j : ℝ) + 1) * √((j : ℝ) + 1)) ≤
      1 / √((j : ℝ) + 1) := by
    apply one_div_le_one_div_of_le hs
    nlinarith
  have hglobal : 6 * √((j : ℝ) + 1) / ((n : ℝ) + 1) ≤
      5 / √((j : ℝ) + 1) := by
    rw [div_le_div_iff₀ hN hs]
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
    have hjr : 2 * (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    nlinarith
  have htri := abs_add_le
    (parkingG n j - 2 / (√(2 * Real.pi) * √((j : ℝ) + 1)))
    (2 / (√(2 * Real.pi) * √((j : ℝ) + 1)))
  rw [sub_add_cancel, abs_of_nonneg (by positivity :
    0 ≤ 2 / (√(2 * Real.pi) * √((j : ℝ) + 1)))] at htri
  calc _ ≤ 1 / √((j : ℝ) + 1) + 5 / √((j : ℝ) + 1) +
      1 / √((j : ℝ) + 1) := by linarith
    _ = _ := by ring

/-- Squaring the manuscript's sharp half-range expansion gives the required
`O(j⁻² + n⁻¹)` pointwise error, before reflection and summation. -/
theorem abs_parkingG_sq_sub_le_endpoint (n : ℕ+) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ)) :
    |parkingG n j ^ 2 - 2 / Real.pi * (1 / ((j : ℝ) + 1))| ≤
      4 / ((j : ℝ) + 1) ^ 2 + 48 / ((n : ℝ) + 1) := by
  let a : ℝ := (j : ℝ) + 1
  let c : ℝ := 2 / (√(2 * Real.pi) * √a)
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : 0 < √a := by positivity
  have hS : 0 < √(2 * Real.pi) := by positivity
  have hS2 : (2 : ℝ) ≤ √(2 * Real.pi) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith [Real.two_le_pi]
  have hc : c ≤ 1 / √a := by
    dsimp [c]
    rw [div_le_div_iff₀ (by positivity) hs]
    nlinarith
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hcsq : c ^ 2 = 2 / Real.pi * (1 / a) := by
    dsimp [c]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt ha.le]
    field_simp
  have hd : |parkingG n j - c| ≤ 1 / (2 * a * √a) + 6 * √a / ((n : ℝ) + 1) :=
    abs_parkingG_sub_borel_leading_le n j hj
  have hg : |parkingG n j| ≤ 7 / √a := abs_parkingG_le_from_borelTail n j hj
  have hplus : |parkingG n j + c| ≤ 8 / √a := by
    have ht := abs_add_le (parkingG n j) c
    rw [abs_of_nonneg hc0] at ht
    calc _ ≤ 7 / √a + 1 / √a := by linarith
      _ = _ := by ring
  change |parkingG n j ^ 2 - 2 / Real.pi * (1 / a)| ≤ 4 / a ^ 2 + 48 / ((n : ℝ) + 1)
  rw [← hcsq, show parkingG n j ^ 2 - c ^ 2 = (parkingG n j - c) * (parkingG n j + c) by ring,
    abs_mul]
  calc _ ≤ (1 / (2 * a * √a) + 6 * √a / ((n : ℝ) + 1)) * (8 / √a) :=
      mul_le_mul hd hplus (abs_nonneg _) (by positivity)
    _ = _ := by
      have hsq := Real.sq_sqrt ha.le
      field_simp
      nlinarith

end Parking
