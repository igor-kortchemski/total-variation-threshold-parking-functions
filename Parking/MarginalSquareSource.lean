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

public import Parking.MarginalBounds

/-!
# The manuscript's pointwise square error, reflection, and summation

This module uses the endpoint/Borel-tail expansion and its sharp square error.
It supplies the error summed by the marginal second-moment theorem.
-/

public section
namespace Parking
open Finset

/-- Reflection of the sharp source square estimate. The summable error is
`O(j⁻² + (n+1-j)⁻² + n⁻¹)` on the entire range. -/
theorem abs_parkingG_sq_sub_le_source_err (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n) :
    |parkingG n j ^ 2 - 2 / Real.pi *
        (1 / (((j : ℕ) + 1 : ℕ) : ℝ) + 1 / (((n : ℕ) - j : ℕ) : ℝ))| ≤
      100 * ((1 / (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 + 1 / (n : ℝ)) +
        (1 / (((n : ℕ) - j : ℕ) : ℝ) ^ 2 + 1 / (n : ℝ))) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  let x : ℝ := (((n : ℕ) - j : ℕ) : ℝ)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ (n : ℕ) - j by omega)
  have hxn : x + (j : ℝ) = n := by
    dsimp [x]
    rw [Nat.cast_sub j.isLt.le]
    ring
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hp : 0 ≤ 2 / Real.pi := by positivity
  have hp1 : 2 / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    exact Real.two_le_pi
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hni : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hn0 (by linarith)
  have ha0 : 0 ≤ 1 / ((j : ℝ) + 1) ^ 2 := by positivity
  have hx0 : 0 ≤ 1 / x ^ 2 := by positivity
  have hnn : 0 ≤ 1 / (n : ℝ) := by positivity
  simp only [Nat.cast_add, Nat.cast_one]
  change |parkingG n j ^ 2 - 2 / Real.pi * (1 / ((j : ℝ) + 1) + 1 / x)| ≤
    100 * ((1 / ((j : ℝ) + 1) ^ 2 + 1 / (n : ℝ)) + (1 / x ^ 2 + 1 / (n : ℝ)))
  rcases le_or_gt (2 * (j : ℕ)) (n : ℕ) with hj | hj
  · have he := abs_le.1 (abs_parkingG_sq_sub_le_endpoint n j hj)
    have hnx : (n : ℝ) ≤ 2 * x := by
      have hjr : 2 * (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
      linarith
    have hext : 2 / Real.pi * (1 / x) ≤ 2 / (n : ℝ) := by
      calc _ ≤ 1 / x := mul_le_of_le_one_left (by positivity) hp1
        _ ≤ _ := by rw [div_le_div_iff₀ (by linarith) hn0]; linarith
    have hext0 : 0 ≤ 2 / Real.pi * (1 / x) := by positivity
    rw [mul_add, abs_le]
    simp only [div_eq_mul_inv, one_mul] at he hni ha0 hx0 hnn hext hext0 ⊢
    constructor <;> linarith only [he.1, he.2, hni, ha0, hx0, hnn, hext, hext0]
  · let k : Fin n := ⟨(n : ℕ) - j, by omega⟩
    have hk : (k : ℝ) = x := rfl
    have hr := parkingG_add_parkingG_of_add_eq n j.isLt k.isLt
      (show (j : ℕ) + (k : ℕ) = (n : ℕ) by dsimp [k]; omega)
    change parkingG n j + parkingG n k = -2 / ((n : ℝ) + 1) at hr
    have he := abs_le.1 (abs_parkingG_sq_sub_le_endpoint n k (by dsimp [k]; omega))
    rw [hk] at he
    have hy : |parkingG n k| ≤ 7 := by
      have h := abs_parkingG_le_from_borelTail n k (by dsimp [k]; omega)
      rw [hk] at h
      refine h.trans ?_
      rw [div_le_iff₀ (by positivity)]
      have hs : (1 : ℝ) ≤ √(x + 1) := by
        rw [Real.le_sqrt' (by norm_num)]
        linarith
      linarith
    have hcross : |1 / ((n : ℝ) + 1) * parkingG n k| ≤ 7 / (n : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / ((n : ℝ) + 1))]
      calc _ ≤ (1 / ((n : ℝ) + 1)) * 7 := mul_le_mul_of_nonneg_left hy (by positivity)
        _ ≤ (1 / (n : ℝ)) * 7 := mul_le_mul_of_nonneg_right hni (by norm_num)
        _ = _ := by ring
    have hcross' := abs_le.1 hcross
    have hsq : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 / (n : ℝ) := by
      rw [one_div_pow]
      apply one_div_le_one_div_of_le hn0
      nlinarith
    have hsq0 : 0 ≤ (1 / ((n : ℝ) + 1)) ^ 2 := by positivity
    have hlocal : 1 / (x + 1) ^ 2 ≤ 1 / x ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hdiff : 0 ≤ 2 / Real.pi * (1 / x - 1 / (x + 1)) ∧
        2 / Real.pi * (1 / x - 1 / (x + 1)) ≤ 1 / x ^ 2 := by
      have heq : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by field_simp; ring
      rw [heq]
      constructor
      · positivity
      · calc _ ≤ 1 / (x * (x + 1)) := mul_le_of_le_one_left (by positivity) hp1
          _ ≤ _ := by apply one_div_le_one_div_of_le (by positivity); nlinarith
    have hext : 0 ≤ 2 / Real.pi * (1 / ((j : ℝ) + 1)) ∧
        2 / Real.pi * (1 / ((j : ℝ) + 1)) ≤ 2 / (n : ℝ) := by
      constructor
      · positivity
      · calc _ ≤ 1 / ((j : ℝ) + 1) := mul_le_of_le_one_left (by positivity) hp1
          _ ≤ _ := by
            rw [div_le_div_iff₀ (by positivity) hn0]
            have hjr : (n : ℝ) < 2 * (j : ℝ) := by exact_mod_cast hj
            linarith
    have hexp : parkingG n j ^ 2 = parkingG n k ^ 2 +
        4 * (1 / ((n : ℝ) + 1) * parkingG n k) + 4 * (1 / ((n : ℝ) + 1)) ^ 2 := by
      have hg : parkingG n j = -2 * (1 / ((n : ℝ) + 1)) - parkingG n k := by
        linear_combination hr
      rw [hg]
      ring
    rw [hexp, abs_le]
    simp only [div_eq_mul_inv, one_mul] at he hni hcross' hsq hsq0 hlocal hdiff hext ha0 hx0 hnn ⊢
    constructor <;> linarith only [he.1, he.2, hni, hcross'.1, hcross'.2,
      hsq, hsq0, hlocal, hdiff.1, hdiff.2, hext.1, hext.2, ha0, hx0, hnn]

/-- Summing the source error `j⁻² + n⁻¹` gives an absolute constant. -/
theorem sum_fin_sq_source_err_le (n : ℕ+) :
    ∑ j : Fin n, (1 / (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 + 1 / (n : ℝ)) ≤ 3 := by
  have hsq : ∑ j : Fin n, 1 / (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => 1 / ((j + 1 : ℕ) : ℝ) ^ 2) n,
      range_eq_Ico, sum_Ico_add' (fun i : ℕ => 1 / (i : ℝ) ^ 2) 0 n 1, zero_add]
    simpa using sum_inv_sq_le (a := 1) le_rfl ((n : ℕ) + 1)
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [mul_one_div, div_self hn0]
  linarith


end Parking
