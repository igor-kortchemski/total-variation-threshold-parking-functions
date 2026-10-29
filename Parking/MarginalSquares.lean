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

public import Parking.MarginalSquareSource
import Mathlib.Algebra.Order.Floor.Semifield
import Parking.SqrtSums

/-!
# The square sum and the joint manuscript marginal lemma

The reconstructed proof of `abs_sum_sq_parkingG_sub_log_le_const` consumes
`abs_parkingG_sq_sub_le_source_err` and `sum_fin_sq_source_err_le` from
`Parking.MarginalSquareSource`: endpoint telescoping, Borel normalization,
infinite-tail expansion, the sharp `O(j⁻²+n⁻¹)` square error, reflection, and
harmonic summation. The constant 1202 and the joint `parkingG_marginal` statement
are preserved. The cubic bound consumes the reconstructed pointwise bound.

The earlier midpoint asymptotic and its weaker square-error helpers remain
available below as alternative proofs. They are not used by the reconstructed
square-sum provider or the joint marginal theorem.
-/

public section

namespace Parking

open Finset

/-! ### Elementary facts -/

/-- `√(2/π) = 2/√(2π)`. -/
theorem sqrt_two_div_pi_eq : √(2 / Real.pi) = 2 / √(2 * Real.pi) := by
  have hpi := Real.pi_pos
  rw [show (2 : ℝ) / Real.pi = 2 ^ 2 / (2 * Real.pi) by
      rw [div_eq_div_iff hpi.ne' (by positivity)]
      ring,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num)]

/-- `2/π ≤ 1`. -/
theorem two_div_pi_le_one : 2 / Real.pi ≤ 1 := by
  rw [div_le_one Real.pi_pos]
  exact Real.two_le_pi

/-- `1/√(2π) ≤ 1/2`. -/
theorem one_div_sqrt_two_pi_le : 1 / √(2 * Real.pi) ≤ 1 / 2 := by
  have h : (2 : ℝ) ≤ √(2 * Real.pi) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith [Real.two_le_pi]
  exact one_div_le_one_div_of_le (by norm_num) h

/-- Shift of the summation index: `∑_{a ≤ i < b} f(i + 1) = ∑_{a+1 ≤ I < b+1} f(I)`. -/
theorem sum_Ico_shift (f : ℝ → ℝ) (a b : ℕ) :
    ∑ i ∈ Ico a b, f ((i : ℝ) + 1) = ∑ I ∈ Ico (a + 1) (b + 1), f (I : ℝ) := by
  rw [← sum_Ico_add' (fun I : ℕ => f (I : ℝ)) a b 1]
  push_cast
  rfl

/-! ### The pointwise asymptotic on the left half -/

/-- Asymptotic of `g_n` on the left half, the middle-point variant of the source asymptotic
(`lem:marginal`): for `n ≥ 2` and `2j ≤ n` (`0`-based),
`|g_n(j + 1) - √(2/π)/√(j + 1)| ≤ (j + 1)^{-3/2} + 7/√n`. -/
theorem abs_parkingG_sub_le (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ)) :
    |parkingG n j - √(2 / Real.pi) / √((j : ℝ) + 1)| ≤
      1 / (((j : ℝ) + 1) * √((j : ℝ) + 1)) + 7 / √(n : ℝ) := by
  set S := √(2 * Real.pi) with hS
  set P := 1 / S with hP
  set M := (n : ℕ) / 2 with hM
  have hmid1 : -1 / ((n : ℝ) + 1) ≤ parkingG n ⟨M, by omega⟩ := (parkingG_middle n hn).1
  have hmid2 : parkingG n ⟨M, by omega⟩ ≤
      -1 / ((n : ℝ) + 1) + 1 / (((M : ℝ) + 1) * √((M : ℝ) + 1)) := (parkingG_middle n hn).2
  have hS0 : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hP0 : 0 < P := by positivity
  have hP2 : P ≤ 1 / 2 := one_div_sqrt_two_pi_le
  have htel : parkingG n j = parkingG n ⟨M, by omega⟩ + ∑ i ∈ Ico (j : ℕ) M, parkingGap n i :=
    parkingG_eq_add_sum n j ⟨M, by omega⟩ (show (j : ℕ) ≤ M by omega)
  -- the sums
  set T := ∑ I ∈ Ico ((j : ℕ) + 1) (M + 1), 1 / ((I : ℝ) * √(I : ℝ)) with hT
  set X := ∑ I ∈ Ico ((j : ℕ) + 1) (M + 1), 1 / ((I : ℝ) ^ 2 * √(I : ℝ)) with hX
  set Y := ∑ I ∈ Ico ((j : ℕ) + 1) (M + 1), 1 / √(I : ℝ) with hY
  set E := ∑ i ∈ Ico (j : ℕ) M,
    (parkingGap n i - P * (1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)))) with hE
  have hT' : ∑ i ∈ Ico (j : ℕ) M, 1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)) = T :=
    sum_Ico_shift (fun x => 1 / (x * √x)) _ _
  have hX' : ∑ i ∈ Ico (j : ℕ) M, 1 / (((i : ℝ) + 1) ^ 2 * √((i : ℝ) + 1)) = X :=
    sum_Ico_shift (fun x => 1 / (x ^ 2 * √x)) _ _
  have hY' : ∑ i ∈ Ico (j : ℕ) M, 1 / √((i : ℝ) + 1) = Y :=
    sum_Ico_shift (fun x => 1 / √x) _ _
  have hsplit : ∑ i ∈ Ico (j : ℕ) M, parkingGap n i = P * T + E := by
    rw [hE, sum_sub_distrib, ← mul_sum, hT']
    ring
  have hEb : |E| ≤ P / 12 * X + 4 * P / ((n : ℝ) + 1) * Y := by
    calc |E| ≤ ∑ i ∈ Ico (j : ℕ) M,
          |parkingGap n i - P * (1 / (((i : ℝ) + 1) * √((i : ℝ) + 1)))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Ico (j : ℕ) M, (P / 12 * (1 / (((i : ℝ) + 1) ^ 2 * √((i : ℝ) + 1))) +
          4 * P / ((n : ℝ) + 1) * (1 / √((i : ℝ) + 1))) := by
          refine sum_le_sum fun i hi => ?_
          have hiM := (mem_Ico.1 hi).2
          have h := abs_parkingGap_sub_le (n := (n : ℕ)) (i := i) (by omega)
          have e1 : P * (1 / (((i : ℝ) + 1) * √((i : ℝ) + 1))) =
              1 / (S * ((i : ℝ) + 1) * √((i : ℝ) + 1)) := by
            rw [hP]
            generalize √((i : ℝ) + 1) = b
            generalize (i : ℝ) + 1 = a
            ring
          have e2 : P / 12 * (1 / (((i : ℝ) + 1) ^ 2 * √((i : ℝ) + 1))) +
              4 * P / ((n : ℝ) + 1) * (1 / √((i : ℝ) + 1)) =
              1 / (12 * S * ((i : ℝ) + 1) ^ 2 * √((i : ℝ) + 1)) +
                4 / (S * ((n : ℝ) + 1) * √((i : ℝ) + 1)) := by
            rw [hP]
            generalize √((i : ℝ) + 1) = b
            generalize (i : ℝ) + 1 = a
            generalize (n : ℝ) + 1 = N
            ring
          rw [e1, e2]
          exact h
      _ = P / 12 * X + 4 * P / ((n : ℝ) + 1) * Y := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, hX', hY']
  -- bounds on the sums
  have hTlow : 2 / √((j : ℝ) + 1) - 2 / √((M : ℝ) + 1) ≤ T := by
    have h := sub_le_sum_inv_mul_sqrt (a := (j : ℕ) + 1) (b := M + 1) (by omega) (by omega)
    push_cast at h
    exact h
  have hTup : T ≤ 1 / (((j : ℝ) + 1) * √((j : ℝ) + 1)) + 2 / √((j : ℝ) + 1) := by
    have h := sum_inv_mul_sqrt_le (a := (j : ℕ) + 1) (by omega) (M + 1)
    push_cast at h
    exact h
  have hXup : X ≤ 2 / (((j : ℝ) + 1) * √((j : ℝ) + 1)) := by
    have h := sum_inv_sq_mul_sqrt_le (a := (j : ℕ) + 1) (by omega) (M + 1)
    push_cast at h
    exact h
  have hX0 : 0 ≤ X := sum_nonneg fun I _ => by positivity
  have hYup : Y ≤ 2 * √((M : ℝ) + 1) := by
    have h := sum_inv_sqrt_le (M + 1)
    have hsub : Y ≤ ∑ I ∈ Ico 1 (M + 1), 1 / √(I : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico (by omega) le_rfl)
        fun I _ _ => by positivity
    push_cast at h
    linarith
  have hY0 : 0 ≤ Y := sum_nonneg fun I _ => by positivity
  -- comparison of the scales
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hMR : 2 * (M : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (M : ℝ) + 1 := by
    constructor
    · exact_mod_cast (show 2 * M ≤ (n : ℕ) by omega)
    · exact_mod_cast (show (n : ℕ) ≤ 2 * M + 1 by omega)
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsM : 0 < √((M : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hsj : 0 < √((j : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hsnn : √(n : ℝ) ≤ (n : ℝ) + 1 := by
    have := Real.sqrt_le_self_iff.2 (Or.inr (show (1 : ℝ) ≤ n by linarith))
    linarith
  have hw1 : 1 / ((n : ℝ) + 1) ≤ 1 / √(n : ℝ) := one_div_le_one_div_of_le hsn hsnn
  have hw2 : 1 / √((M : ℝ) + 1) ≤ 2 * (1 / √(n : ℝ)) := by
    rw [mul_one_div, div_le_div_iff₀ hsM hsn, one_mul]
    have : √(n : ℝ) ≤ √(2 ^ 2 * ((M : ℝ) + 1)) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at this
  have hw3 : 1 / (((M : ℝ) + 1) * √((M : ℝ) + 1)) ≤
      1 / √((M : ℝ) + 1) :=
    one_div_le_one_div_of_le hsM
      (le_mul_of_one_le_left hsM.le (by have : (0 : ℝ) ≤ M := M.cast_nonneg; linarith))
  have hw4 : √((M : ℝ) + 1) / ((n : ℝ) + 1) ≤ 1 / √(n : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hsn, one_mul]
    have h1 : √((M : ℝ) + 1) ≤ √(n : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have h2 : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by linarith)
    nlinarith
  -- the error terms
  have hE1 : P / 12 * X ≤ 1 / 12 * (1 / (((j : ℝ) + 1) * √((j : ℝ) + 1))) := by
    calc P / 12 * X ≤ (1 / 2) / 12 * (2 / (((j : ℝ) + 1) * √((j : ℝ) + 1))) :=
          mul_le_mul (by linarith) hXup hX0 (by norm_num)
      _ = 1 / 12 * (1 / (((j : ℝ) + 1) * √((j : ℝ) + 1))) := by ring
  have hE2 : 4 * P / ((n : ℝ) + 1) * Y ≤ 4 * (1 / √(n : ℝ)) := by
    calc 4 * P / ((n : ℝ) + 1) * Y ≤ 4 * (1 / 2) / ((n : ℝ) + 1) * (2 * √((M : ℝ) + 1)) :=
          mul_le_mul (by gcongr) hYup hY0 (by positivity)
      _ = 4 * (√((M : ℝ) + 1) / ((n : ℝ) + 1)) := by ring
      _ ≤ 4 * (1 / √(n : ℝ)) := by linarith
  have hEabs := abs_le.1 (hEb.trans (add_le_add hE1 hE2))
  -- the main term
  have hmain1 : P * (T - 2 / √((j : ℝ) + 1)) ≤
      1 / 2 * (1 / (((j : ℝ) + 1) * √((j : ℝ) + 1))) := by
    calc P * (T - 2 / √((j : ℝ) + 1)) ≤ P * (1 / (((j : ℝ) + 1) * √((j : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (by linarith) hP0.le
      _ ≤ 1 / 2 * (1 / (((j : ℝ) + 1) * √((j : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right hP2 (by positivity)
  have hmain2 : -(1 / √((M : ℝ) + 1)) ≤ P * (T - 2 / √((j : ℝ) + 1)) := by
    have h1 : P * (-(2 / √((M : ℝ) + 1))) ≤ P * (T - 2 / √((j : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hP0.le
    have h2 : P * (1 / √((M : ℝ) + 1)) ≤ 1 / 2 * (1 / √((M : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hP2 (by positivity)
    have e : P * (-(2 / √((M : ℝ) + 1))) = -2 * (P * (1 / √((M : ℝ) + 1))) := by ring
    linarith
  have ha : √(2 / Real.pi) / √((j : ℝ) + 1) = 2 * P / √((j : ℝ) + 1) := by
    rw [sqrt_two_div_pi_eq, hP]
    ring
  have hdec : parkingG n j - √(2 / Real.pi) / √((j : ℝ) + 1) =
      parkingG n ⟨M, by omega⟩ + P * (T - 2 / √((j : ℝ) + 1)) + E := by
    rw [htel, hsplit, ha]
    ring
  have e1 : -1 / ((n : ℝ) + 1) = -(1 / ((n : ℝ) + 1)) := by ring
  have e7 : 7 / √(n : ℝ) = 7 * (1 / √(n : ℝ)) := by ring
  have hu0 : 0 ≤ 1 / (((j : ℝ) + 1) * √((j : ℝ) + 1)) := by positivity
  have hw0 : 0 ≤ 1 / √(n : ℝ) := by positivity
  have hn0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  rw [hdec, abs_le, e7]
  constructor <;> linarith

/-! ### Squares -/

/-- Squares on the left half: for `n ≥ 2` and `2j ≤ n` (`0`-based),
`|g_n(j + 1)² - (2/π)/(j + 1)| ≤ 8/(j + 1)² + 56/(√n √(j + 1))`. With
`a = √(2/π)/√(j + 1)`, this is `|g - a| |g + a|`, where `|g - a|` is bounded by
`abs_parkingG_sub_le` and `|g + a| ≤ 8/√(j + 1)`. -/
theorem abs_parkingG_sq_sub_le (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ)) :
    |parkingG n j ^ 2 - 2 / Real.pi * (1 / ((j : ℝ) + 1))| ≤
      8 * (1 / ((j : ℝ) + 1) ^ 2) + 56 * (1 / √(n : ℝ) * (1 / √((j : ℝ) + 1))) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith
  have hs : 0 < √((j : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
  have hss : √((j : ℝ) + 1) * √((j : ℝ) + 1) = (j : ℝ) + 1 := Real.mul_self_sqrt (by linarith)
  have hd := abs_parkingG_sub_le n hn j hj
  have hg := abs_parkingG_le_of_two_mul_le n hn j hj
  have ha0 : 0 ≤ √(2 / Real.pi) / √((j : ℝ) + 1) := by positivity
  have hav : √(2 / Real.pi) / √((j : ℝ) + 1) ≤ 1 / √((j : ℝ) + 1) := by
    gcongr
    exact (Real.sqrt_le_sqrt two_div_pi_le_one).trans_eq Real.sqrt_one
  have ha2 : (√(2 / Real.pi) / √((j : ℝ) + 1)) ^ 2 = 2 / Real.pi * (1 / ((j : ℝ) + 1)) := by
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith)]
    ring
  have hplus : |parkingG n j + √(2 / Real.pi) / √((j : ℝ) + 1)| ≤ 8 * (1 / √((j : ℝ) + 1)) := by
    calc |parkingG n j + √(2 / Real.pi) / √((j : ℝ) + 1)| ≤
          |parkingG n j| + |√(2 / Real.pi) / √((j : ℝ) + 1)| := abs_add_le _ _
      _ ≤ 7 * (1 / √((j : ℝ) + 1)) + 1 / √((j : ℝ) + 1) := by
          rw [abs_of_nonneg ha0, mul_one_div]
          exact add_le_add hg hav
      _ = 8 * (1 / √((j : ℝ) + 1)) := by ring
  have huv : 1 / (((j : ℝ) + 1) * √((j : ℝ) + 1)) * (1 / √((j : ℝ) + 1)) =
      1 / ((j : ℝ) + 1) ^ 2 := by
    rw [one_div_mul_one_div, mul_assoc, hss, sq]
  rw [← ha2, show parkingG n j ^ 2 - (√(2 / Real.pi) / √((j : ℝ) + 1)) ^ 2 =
      (parkingG n j - √(2 / Real.pi) / √((j : ℝ) + 1)) *
        (parkingG n j + √(2 / Real.pi) / √((j : ℝ) + 1)) by ring, abs_mul]
  calc |parkingG n j - √(2 / Real.pi) / √((j : ℝ) + 1)| *
        |parkingG n j + √(2 / Real.pi) / √((j : ℝ) + 1)| ≤
        (1 / (((j : ℝ) + 1) * √((j : ℝ) + 1)) + 7 / √(n : ℝ)) * (8 * (1 / √((j : ℝ) + 1))) :=
        mul_le_mul hd hplus (abs_nonneg _) (by positivity)
    _ = 8 * (1 / (((j : ℝ) + 1) * √((j : ℝ) + 1)) * (1 / √((j : ℝ) + 1))) +
        56 * (1 / √(n : ℝ) * (1 / √((j : ℝ) + 1))) := by ring
    _ = 8 * (1 / ((j : ℝ) + 1) ^ 2) + 56 * (1 / √(n : ℝ) * (1 / √((j : ℝ) + 1))) := by
        rw [huv]

/-- Squares for every `j` (`0`-based), `n ≥ 2`:
`|g_n(j + 1)² - (2/π)(1/(j + 1) + 1/(n - j))| ≤ 100 (e(j + 1) + e(n - j))`, where
`e(I) = 1/I² + 1/(√n √I)`. On the left half `2j ≤ n` this is `abs_parkingG_sq_sub_le`, with
`1/(n - j) ≤ 2/n`. On the right half, the reflection `g_n(j + 1) = -2/(n + 1) - g_n(k + 1)`
with `k = n - j` brings it back to the left half. -/
theorem abs_parkingG_sq_sub_le_err (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n) :
    |parkingG n j ^ 2 - 2 / Real.pi *
        (1 / (((j : ℕ) + 1 : ℕ) : ℝ) + 1 / (((n : ℕ) - j : ℕ) : ℝ))| ≤
      100 * ((1 / (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 +
          1 / √(n : ℝ) * (1 / √(((j : ℕ) + 1 : ℕ) : ℝ))) +
        (1 / (((n : ℕ) - j : ℕ) : ℝ) ^ 2 + 1 / √(n : ℝ) * (1 / √(((n : ℕ) - j : ℕ) : ℝ)))) := by
  have hjn := j.isLt
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hnn : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hpi0 : 0 ≤ 2 / Real.pi := by positivity
  have hpi1 := two_div_pi_le_one
  have hw0 : 0 ≤ 1 / √(n : ℝ) := by positivity
  rw [show ((((j : ℕ) + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 by push_cast; ring]
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (((n : ℕ) - j : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hx]
  have hx1 : 1 ≤ x := by
    rw [hx]
    exact_mod_cast (show 1 ≤ (n : ℕ) - j by omega)
  have hxn : x + (j : ℝ) = n := by
    rw [hx, Nat.cast_sub hjn.le]
    ring
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hsj : 0 < √((j : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
  have hsx : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hp1 : 0 ≤ 1 / ((j : ℝ) + 1) ^ 2 := by positivity
  have hp2 : 0 ≤ 1 / √(n : ℝ) * (1 / √((j : ℝ) + 1)) := by positivity
  have hp3 : 0 ≤ 1 / x ^ 2 := by positivity
  have hp4 : 0 ≤ 1 / √(n : ℝ) * (1 / √x) := by positivity
  rcases le_or_gt (2 * (j : ℕ)) (n : ℕ) with hj | hj
  · -- left half
    have h2 := abs_parkingG_sq_sub_le n hn j hj
    have hxn2 : (n : ℝ) ≤ 2 * x := by
      have : 2 * (j : ℝ) ≤ n := by exact_mod_cast hj
      linarith
    have hsjn : √((j : ℝ) + 1) ≤ √(n : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (show (j : ℕ) + 1 ≤ (n : ℕ) by omega))
    have hF : 1 / x ≤ 2 * (1 / √(n : ℝ) * (1 / √((j : ℝ) + 1))) := by
      rw [show 2 * (1 / √(n : ℝ) * (1 / √((j : ℝ) + 1))) = 2 / (√(n : ℝ) * √((j : ℝ) + 1)) by
          ring, div_le_div_iff₀ (by linarith) (by positivity)]
      have := mul_le_mul_of_nonneg_left hsjn (Real.sqrt_nonneg (n : ℝ))
      linarith
    have hF' : 2 / Real.pi * (1 / x) ≤ 1 / x := mul_le_of_le_one_left (by positivity) hpi1
    have hF0 : 0 ≤ 2 / Real.pi * (1 / x) := by positivity
    have h2' := abs_le.1 h2
    rw [mul_add, abs_le]
    constructor <;> linarith
  · -- right half, by reflection
    obtain ⟨k, hk⟩ : ∃ k : Fin n, (k : ℕ) = (n : ℕ) - j := ⟨⟨(n : ℕ) - j, by omega⟩, rfl⟩
    have hr : parkingG n j + parkingG n k = -2 / ((n : ℝ) + 1) :=
      parkingG_add_parkingG_of_add_eq n j.isLt k.isLt (by omega)
    have hxk : ((k : ℕ) : ℝ) = x := by rw [hx, hk]
    have h2 := abs_parkingG_sq_sub_le n hn k (by omega)
    have hy := abs_parkingG_le_of_two_mul_le n hn k (by omega)
    rw [hxk] at h2 hy
    have hg : parkingG n j = -2 * (1 / ((n : ℝ) + 1)) - parkingG n k := by
      linear_combination hr
    generalize parkingG n k = y at hg h2 hy
    rw [hg]
    have hsx1 : 0 < √(x + 1) := Real.sqrt_pos.2 (by linarith)
    have hxle : x ≤ (n : ℝ) := by linarith
    have hF2 : 1 / (x + 1) ^ 2 ≤ 1 / x ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
    have hF3 : 1 / √(x + 1) ≤ 1 / √x :=
      one_div_le_one_div_of_le hsx (Real.sqrt_le_sqrt (by linarith))
    have hF4 : 1 / √(n : ℝ) * (1 / √(x + 1)) ≤ 1 / √(n : ℝ) * (1 / √x) :=
      mul_le_mul_of_nonneg_left hF3 hw0
    have hqw : 1 / ((n : ℝ) + 1) ≤ 1 / √(n : ℝ) := by
      refine one_div_le_one_div_of_le hsn ?_
      have := Real.sqrt_le_self_iff.2 (Or.inr (show (1 : ℝ) ≤ n by linarith))
      linarith
    have hF7 : |1 / ((n : ℝ) + 1) * y| ≤ 7 * (1 / √(n : ℝ) * (1 / √x)) := by
      calc |1 / ((n : ℝ) + 1) * y| = 1 / ((n : ℝ) + 1) * |y| := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ 1 / √(n : ℝ) * (7 * (1 / √(x + 1))) :=
            mul_le_mul hqw (by rw [mul_one_div]; exact hy) (abs_nonneg _) hw0
        _ = 7 * (1 / √(n : ℝ) * (1 / √(x + 1))) := by ring
        _ ≤ 7 * (1 / √(n : ℝ) * (1 / √x)) := by linarith
    have hF8 : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 / x ^ 2 := by
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / x := one_div_le_one_div_of_le (by linarith) (by linarith)
      exact (pow_le_pow_left₀ (by positivity) h1 2).trans_eq (one_div_pow x 2)
    have hF9e : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
      field_simp
      ring
    have hF9a : 0 ≤ 1 / x - 1 / (x + 1) := by
      rw [hF9e]
      positivity
    have hF9b : 1 / x - 1 / (x + 1) ≤ 1 / x ^ 2 := by
      rw [hF9e]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hF9c : 0 ≤ 2 / Real.pi * (1 / x - 1 / (x + 1)) := mul_nonneg hpi0 hF9a
    have hF9d : 2 / Real.pi * (1 / x - 1 / (x + 1)) ≤ 1 / x ^ 2 :=
      (mul_le_of_le_one_left hF9a hpi1).trans hF9b
    have hF10 : 1 / ((j : ℝ) + 1) ≤ 2 * (1 / √(n : ℝ) * (1 / √x)) := by
      rw [show 2 * (1 / √(n : ℝ) * (1 / √x)) = 2 / (√(n : ℝ) * √x) by ring,
        div_le_div_iff₀ (by linarith) (by positivity)]
      have hsxn : √x ≤ √(n : ℝ) := Real.sqrt_le_sqrt hxle
      have := mul_le_mul_of_nonneg_left hsxn (Real.sqrt_nonneg (n : ℝ))
      have : (n : ℝ) < 2 * (j : ℝ) := by exact_mod_cast hj
      linarith
    have hF10' : 2 / Real.pi * (1 / ((j : ℝ) + 1)) ≤ 1 / ((j : ℝ) + 1) :=
      mul_le_of_le_one_left (by positivity) hpi1
    have hF10'' : 0 ≤ 2 / Real.pi * (1 / ((j : ℝ) + 1)) := by positivity
    have hexp : (-2 * (1 / ((n : ℝ) + 1)) - y) ^ 2 =
        4 * (1 / ((n : ℝ) + 1)) ^ 2 + 4 * (1 / ((n : ℝ) + 1) * y) + y ^ 2 := by ring
    have hq2 : 0 ≤ (1 / ((n : ℝ) + 1)) ^ 2 := by positivity
    have h2' := abs_le.1 h2
    have hF7' := abs_le.1 hF7
    rw [hexp, abs_le]
    constructor <;> linarith

/-! ### The square sum -/

/-- The error scale summed over the range: `∑_{j < n} (1/(j + 1)² + 1/(√n √(j + 1))) ≤ 6`,
from `∑_{I ≥ 1} 1/I² ≤ 2` and `∑_{1 ≤ I ≤ n} 1/√I ≤ 2 √(n + 1) ≤ 4 √n`. -/
theorem sum_fin_sq_err_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ j : Fin n, (1 / ((((j : ℕ) + 1 : ℕ)) : ℝ) ^ 2 +
      1 / √(n : ℝ) * (1 / √((((j : ℕ) + 1 : ℕ)) : ℝ))) ≤ 6 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => 1 / (((j + 1 : ℕ)) : ℝ) ^ 2 +
      1 / √(n : ℝ) * (1 / √(((j + 1 : ℕ)) : ℝ))) n, range_eq_Ico,
    sum_Ico_add' (fun I : ℕ => 1 / (I : ℝ) ^ 2 + 1 / √(n : ℝ) * (1 / √(I : ℝ))) 0 n 1,
    zero_add, sum_add_distrib, ← mul_sum]
  have h1 := sum_inv_sq_le (a := 1) le_rfl (n + 1)
  have h2 := sum_inv_sqrt_le (n + 1)
  push_cast at h1 h2
  rw [div_one] at h1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have h3 : 1 / √(n : ℝ) * (2 * √((n : ℝ) + 1)) ≤ 4 := by
    rw [show 1 / √(n : ℝ) * (2 * √((n : ℝ) + 1)) = 2 * √((n : ℝ) + 1) / √(n : ℝ) by ring,
      div_le_iff₀ hsn]
    have : √((n : ℝ) + 1) ≤ √(2 ^ 2 * (n : ℝ)) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at this
    linarith
  have h4 : 1 / √(n : ℝ) * ∑ I ∈ Ico 1 (n + 1), 1 / √(I : ℝ) ≤
      1 / √(n : ℝ) * (2 * √((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- The square-sum estimate of `eq:g_moments` (`lem:marginal`) with an explicit constant:
`|∑_j g_n(j)² - (4/π) log n| ≤ 1202` for `n ≥ 2`. Summing `abs_parkingG_sq_sub_le_source_err`, the
main terms give `(2/π) ∑_j (1/(j + 1) + 1/(n - j)) = (4/π) H_n`, with
`log n ≤ H_n ≤ 1 + log n`. The source error sums to at most 3; the
previous constant is preserved by the harmless bound `3 ≤ 6`. -/
theorem abs_sum_sq_parkingG_sub_log_le_const (n : ℕ+) (hn : 2 ≤ (n : ℕ)) :
    |∑ j, parkingG n j ^ 2 - 4 / Real.pi * Real.log n| ≤ 1202 := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun I : ℕ => 1 / (I : ℝ) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ,
      e = fun I : ℕ => 1 / (I : ℝ) ^ 2 + 1 / (n : ℝ) := ⟨_, rfl⟩
  have hterm : ∀ j : Fin n, |parkingG n j ^ 2 - 2 / Real.pi * (f ((j : ℕ) + 1) + f ((n : ℕ) - j))| ≤
      100 * (e ((j : ℕ) + 1) + e ((n : ℕ) - j)) := by
    intro j
    rw [hf, he]
    exact abs_parkingG_sq_sub_le_source_err n hn j
  have hH : ∑ j : Fin n, f ((j : ℕ) + 1) = ∑ j : Fin n, 1 / ((j : ℝ) + 1) := by
    simp only [hf, Nat.cast_add, Nat.cast_one]
  have hmain : ∑ j : Fin n, 2 / Real.pi * (f ((j : ℕ) + 1) + f ((n : ℕ) - j)) =
      4 / Real.pi * ∑ j : Fin n, 1 / ((j : ℝ) + 1) := by
    rw [← mul_sum, sum_add_distrib, sum_fin_reflect f, hH]
    ring
  have herr : ∑ j : Fin n, e ((j : ℕ) + 1) ≤ 6 := by
    simp only [he]
    exact (sum_fin_sq_source_err_le n).trans (by norm_num)
  have hsum_err : |∑ j : Fin n,
      (parkingG n j ^ 2 - 2 / Real.pi * (f ((j : ℕ) + 1) + f ((n : ℕ) - j)))| ≤ 1200 := by
    calc |∑ j : Fin n,
          (parkingG n j ^ 2 - 2 / Real.pi * (f ((j : ℕ) + 1) + f ((n : ℕ) - j)))| ≤
          ∑ j : Fin n,
            |parkingG n j ^ 2 - 2 / Real.pi * (f ((j : ℕ) + 1) + f ((n : ℕ) - j))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, 100 * (e ((j : ℕ) + 1) + e ((n : ℕ) - j)) :=
          sum_le_sum fun j _ => hterm j
      _ = 200 * ∑ j : Fin n, e ((j : ℕ) + 1) := by
          rw [← mul_sum, sum_add_distrib, sum_fin_reflect e]
          ring
      _ ≤ 200 * 6 := mul_le_mul_of_nonneg_left herr (by norm_num)
      _ = 1200 := by norm_num
  have hdec : ∑ j, parkingG n j ^ 2 - 4 / Real.pi * Real.log n =
      ∑ j : Fin n, (parkingG n j ^ 2 - 2 / Real.pi * (f ((j : ℕ) + 1) + f ((n : ℕ) - j))) +
        4 / Real.pi * (∑ j : Fin n, 1 / ((j : ℝ) + 1) - Real.log n) := by
    rw [sum_sub_distrib, hmain]
    ring
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog1 : Real.log n ≤ ∑ j : Fin n, 1 / ((j : ℝ) + 1) :=
    (Real.log_le_log (by linarith) (by linarith)).trans (log_add_one_le_sum_inv n)
  have hlog2 := sum_inv_le_one_add_log n
  have hpi0 : 0 ≤ 4 / Real.pi := by positivity
  have hpi2 : 4 / Real.pi ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.two_le_pi]
  have hA : 0 ≤ 4 / Real.pi * (∑ j : Fin n, 1 / ((j : ℝ) + 1) - Real.log n) :=
    mul_nonneg hpi0 (by linarith)
  have hB : 4 / Real.pi * (∑ j : Fin n, 1 / ((j : ℝ) + 1) - Real.log n) ≤ 4 / Real.pi * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hpi0
  have hsum_err' := abs_le.1 hsum_err
  rw [hdec, abs_le]
  constructor <;> linarith

/-- The square-sum estimate of `eq:g_moments` (`lem:marginal`):
`∑_j g_n(j)² = (4/π) log n + O(1)`, uniformly in `n ≥ 2`. -/
theorem exists_abs_sum_sq_parkingG_sub_log_le : ∃ C : ℝ, ∀ n : ℕ+, 2 ≤ (n : ℕ) →
    |∑ j, parkingG n j ^ 2 - 4 / Real.pi * Real.log n| ≤ C :=
  ⟨1202, abs_sum_sq_parkingG_sub_log_le_const⟩

/-- `∑_j g_n(j)² ≍ log n` for `n ≥ 2` (`lem:marginal`). The upper bound uses
`log n ≥ log 2 > 0`. For the lower bound: if `log n ≥ 2404`, then
`∑_j g_n(j)² ≥ (4/π) log n - 1202 ≥ log n / 2`; otherwise `∑_j g_n(j)² ≥ g_n(1)² ≥ 1/9`. -/
theorem exists_sum_sq_parkingG_comparable : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) →
    c * Real.log n ≤ ∑ j, parkingG n j ^ 2 ∧ ∑ j, parkingG n j ^ 2 ≤ C * Real.log n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / 22000, 2 + 1202 / Real.log 2, by norm_num,
    add_pos (by norm_num) (div_pos (by norm_num) hl2), fun n hn => ?_⟩
  have h := abs_le.1 (abs_sum_sq_parkingG_sub_log_le_const n hn)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hl0 : 0 ≤ Real.log n := by linarith
  have hpi1 : 1 ≤ 4 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith [Real.pi_le_four]
  have hpi2 : 4 / Real.pi ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.two_le_pi]
  constructor
  · have hg0 : 1 / 9 ≤ ∑ j, parkingG n j ^ 2 := by
      have h0 : 1 / 3 ≤ parkingG n ⟨0, n.pos⟩ := by
        rw [parkingG_zero, div_le_div_iff₀ (by norm_num) (by linarith)]
        linarith
      calc (1 / 9 : ℝ) = (1 / 3) ^ 2 := by norm_num
        _ ≤ parkingG n ⟨0, n.pos⟩ ^ 2 := pow_le_pow_left₀ (by norm_num) h0 2
        _ ≤ ∑ j, parkingG n j ^ 2 :=
            single_le_sum (f := fun j => parkingG n j ^ 2) (fun j _ => sq_nonneg _) (mem_univ _)
    rcases le_total (Real.log n) 2404 with hL | hL
    · linarith
    · have := mul_le_mul_of_nonneg_right hpi1 hl0
      linarith
  · have h1 := mul_le_mul_of_nonneg_right hpi2 hl0
    have h2 : 1202 / Real.log 2 * Real.log 2 = 1202 := div_mul_cancel₀ _ hl2.ne'
    have h3 : 1202 / Real.log 2 * Real.log 2 ≤ 1202 / Real.log 2 * Real.log n :=
      mul_le_mul_of_nonneg_left hlog2 (div_pos (by norm_num) hl2).le
    linarith

/-! ### The assembled lemma -/

/-- `lem:marginal`. -/
theorem parkingG_marginal :
    (∀ n : ℕ+, Antitone (parkingG n)) ∧
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) →
      (∀ j : Fin n, Real.exp (-1) ≤ 1 + parkingG n j ∧ 1 + parkingG n j ≤ 2 ∧
          |parkingG n j| ≤ C / √((min ((j : ℕ) + 1) ((n : ℕ) - j) : ℕ) : ℝ)) ∧
      (∀ j : Fin n, (j : ℕ) + 1 ≤ max 1 ⌊ε * (n : ℝ)⌋₊ → c / √((j : ℝ) + 1) ≤ parkingG n j) ∧
      |∑ j, parkingG n j ^ 2 - 4 / Real.pi * Real.log n| ≤ C ∧
      ∑ j, |parkingG n j| ^ 3 ≤ C := by
  refine ⟨parkingG_antitone, 1 / 25, 6000, 1 / 100, by norm_num, by norm_num, by norm_num,
    fun n hn => ⟨fun j => ⟨exp_neg_one_le_one_add_parkingG n hn j, one_add_parkingG_le_two n j,
      ?_⟩, fun j hj => ?_, ?_, ?_⟩⟩
  · calc |parkingG n j| ≤ 10 / √((min ((j : ℕ) + 1) ((n : ℕ) - j) : ℕ) : ℝ) :=
          abs_parkingG_le n hn j
      _ ≤ 6000 / √((min ((j : ℕ) + 1) ((n : ℕ) - j) : ℕ) : ℝ) := by gcongr; norm_num
  · have hfl : ⌊(1 / 100 : ℝ) * ((n : ℕ) : ℝ)⌋₊ = (n : ℕ) / 100 := by
      rw [show (1 / 100 : ℝ) * ((n : ℕ) : ℝ) = ((n : ℕ) : ℝ) / ((100 : ℕ) : ℝ) by
        push_cast
        ring]
      exact Nat.floor_div_eq_div (n : ℕ) 100
    rw [hfl] at hj
    rw [div_div]
    exact parkingG_ge_of_le n hn j hj
  · exact (abs_sum_sq_parkingG_sub_log_le_const n hn).trans (by norm_num)
  · exact sum_abs_parkingG_pow_three_le n hn

end Parking

end
