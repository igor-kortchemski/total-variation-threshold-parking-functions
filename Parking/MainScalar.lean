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

public import Parking.ProxySums
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scalar steps of the proof of `thm:main`

This module proves the scalar
inequalities used in the proof of `thm:main`, with
`b = b_{n,k} = k log(k + 1) / n` (`Parking.bScale`) and `L = log (k + 1)`.

* `decoupling_le_three_mul_bScale` (an auxiliary scalar estimate): for `n ≥ 2` and `1 ≤ k ≤ n`,
  `k (k - 1) log n / (2 n (n - 1)) ≤ 3 b √b`. The left side is the square of the total
  variation bound given by `prop:decoupling`. The proof uses `(k - 1) / (n - 1) ≤ k / n`,
  then `√k log n ≤ √n (L + 2)` (write `log n = log k + 2 log (√n / √k)` and use
  `log y ≤ y - 1`), and finally `(L + 2)² ≤ 36 L³` for `L ≥ log 2`.
* `log_add_one_le_two_mul_log`: `log (k + 1) ≤ 2 log n` for `k ≤ n`, `n ≥ 2`.
* `sqrt_div_add_le_one_sub_exp` (Large-scale lower bound in `thm:main`, scalar part):
  `√(b / (C + b)) ≤ 1 - e^{-c b}` for `b ≥ b₀` and `C ≥ 2 / c + 1 / (c² b₀)`, through
  `1 - e^{-x} ≥ x / (1 + x)`.
* `sqrt_div_add_le_mul_sqrt` (Final lower bound in `thm:main`, scalar part):
  `√(b / (C + b)) ≤ c √b` for `C ≥ 1 / c²`.
* `sum_sq_div_le_one_sub_mean_sqrt` (Square-root sum estimate): if `∑ⱼ gⱼ = 0` and
  `0 ≤ 1 + gⱼ ≤ 2`, then `∑ⱼ gⱼ² / (2 n (1 + √2)²) ≤ 1 - (1/n) ∑ⱼ √(1 + gⱼ)`, from the
  identity `1 - (1/n) ∑ⱼ √(1 + gⱼ) = (1 / (2n)) ∑ⱼ (√(1 + gⱼ) - 1)²`.
* `div_add_eq_bScale`: `k L / (C n + k L) = b / (C + b)`.
-/

public section

namespace Parking

/-- An auxiliary scalar estimate: for `n ≥ 2` and `1 ≤ k ≤ n`, the square
`k (k - 1) log n / (2 n (n - 1))` of the decoupling bound is at most `3 b √b`, with
`b = b_{n,k} = k log (k + 1) / n`. -/
theorem decoupling_le_three_mul_bScale {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (k : ℝ) * ((k : ℝ) - 1) * Real.log n / (2 * n * ((n : ℝ) - 1)) ≤
      3 * bScale n k * √(bScale n k) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hlog2 := Real.log_two_gt_d9
  have hL2 : Real.log 2 ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hLpos : 0 < Real.log ((k : ℝ) + 1) := by linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk'
  have hlogkL : Real.log k ≤ Real.log ((k : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  -- `√k log n ≤ √n (L + 2)`, squared.
  have hmain : (k : ℝ) * Real.log n ^ 2 ≤ n * (Real.log ((k : ℝ) + 1) + 2) ^ 2 := by
    have hs0 : 0 < √(k : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hst : √(k : ℝ) ≤ √(n : ℝ) := Real.sqrt_le_sqrt hkn'
    have hsplit : Real.log n = Real.log k + 2 * Real.log (√(n : ℝ) / √(k : ℝ)) := by
      rw [Real.log_div (Real.sqrt_pos.2 (by linarith)).ne' hs0.ne',
        Real.log_sqrt (by linarith), Real.log_sqrt (by linarith)]
      ring
    have hy : Real.log (√(n : ℝ) / √(k : ℝ)) ≤ √(n : ℝ) / √(k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hs0.trans_le hst) hs0)
    have hA : √(k : ℝ) * Real.log k ≤ √(n : ℝ) * Real.log ((k : ℝ) + 1) :=
      mul_le_mul hst hlogkL hlogk (Real.sqrt_nonneg _)
    have hB : √(k : ℝ) * Real.log (√(n : ℝ) / √(k : ℝ)) ≤ √(n : ℝ) - √(k : ℝ) := by
      have := mul_le_mul_of_nonneg_left hy hs0.le
      rwa [mul_sub, mul_div_cancel₀ _ hs0.ne', mul_one] at this
    have hC : √(k : ℝ) * Real.log n ≤ √(n : ℝ) * (Real.log ((k : ℝ) + 1) + 2) := by
      rw [hsplit]
      nlinarith
    have hC0 : 0 ≤ √(k : ℝ) * Real.log n := mul_nonneg hs0.le hlogn
    calc (k : ℝ) * Real.log n ^ 2 = (√(k : ℝ) * Real.log n) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by linarith)]
      _ ≤ (√(n : ℝ) * (Real.log ((k : ℝ) + 1) + 2)) ^ 2 := pow_le_pow_left₀ hC0 hC 2
      _ = n * (Real.log ((k : ℝ) + 1) + 2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by linarith)]
  -- `(L + 2)² ≤ 36 L³` for `L ≥ log 2`.
  have hcube : (Real.log ((k : ℝ) + 1) + 2) ^ 2 ≤ 36 * Real.log ((k : ℝ) + 1) ^ 3 := by
    have h1 : 0 ≤ Real.log ((k : ℝ) + 1) - 0.69 := by linarith
    nlinarith [mul_nonneg h1 (sq_nonneg (Real.log ((k : ℝ) + 1))), mul_nonneg h1 hLpos.le]
  have hbS : bScale n k = k * Real.log ((k : ℝ) + 1) / n := rfl
  have hn0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  -- `k log n / (6 n L) ≤ √b`.
  have hsqrt : (k : ℝ) * Real.log n / (6 * n * Real.log ((k : ℝ) + 1)) ≤ √(bScale n k) := by
    apply Real.le_sqrt_of_sq_le
    rw [hbS, div_pow, div_le_div_iff₀ (by positivity) hn0]
    have h1 : (k : ℝ) * Real.log n ^ 2 ≤ 36 * n * Real.log ((k : ℝ) + 1) ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hcube hn0.le]
    calc ((k : ℝ) * Real.log n) ^ 2 * n = (k * n) * (k * Real.log n ^ 2) := by ring
      _ ≤ (k * n) * (36 * n * Real.log ((k : ℝ) + 1) ^ 3) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = k * Real.log ((k : ℝ) + 1) * (6 * n * Real.log ((k : ℝ) + 1)) ^ 2 := by ring
  calc (k : ℝ) * ((k : ℝ) - 1) * Real.log n / (2 * n * ((n : ℝ) - 1))
      ≤ (k : ℝ) * k * Real.log n / (2 * n * n) := by
        rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
        have h1 : (k : ℝ) * ((k : ℝ) - 1) * (2 * n * n) ≤ k * k * (2 * n * ((n : ℝ) - 1)) := by
          nlinarith [mul_le_mul_of_nonneg_left hkn' (by positivity : (0 : ℝ) ≤ 2 * k * n)]
        nlinarith [mul_le_mul_of_nonneg_right h1 hlogn]
    _ = 3 * (k * Real.log ((k : ℝ) + 1) / n) *
          ((k : ℝ) * Real.log n / (6 * n * Real.log ((k : ℝ) + 1))) := by
        field_simp
        ring
    _ ≤ 3 * bScale n k * √(bScale n k) := by
        rw [hbS]
        exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- `log (k + 1) ≤ 2 log n` for `n ≥ 2` and `k ≤ n`, since `k + 1 ≤ n + 1 ≤ n²`. -/
theorem log_add_one_le_two_mul_log {n k : ℕ} (hn : 2 ≤ n) (hkn : k ≤ n) :
    Real.log ((k : ℝ) + 1) ≤ 2 * Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
  exact Real.log_le_log (by linarith) (by nlinarith)

/-- Scalar part of Large-scale lower bound in `thm:main`: if `c > 0`, `b₀ > 0`, `C ≥ 2 / c + 1 / (c² b₀)` and
`b ≥ b₀`, then `√(b / (C + b)) ≤ 1 - e^{-c b}`. -/
theorem sqrt_div_add_le_one_sub_exp {c b₀ C b : ℝ} (hc : 0 < c) (hb₀ : 0 < b₀)
    (hC : 2 / c + 1 / (c ^ 2 * b₀) ≤ C) (hb : b₀ ≤ b) :
    √(b / (C + b)) ≤ 1 - Real.exp (-(c * b)) := by
  have hb0 : 0 < b := hb₀.trans_le hb
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  have hx0 : 0 < c * b := mul_pos hc hb0
  -- `1 - e^{-x} ≥ x / (1 + x)` for `x = c b ≥ 0`.
  have hexp : Real.exp (-(c * b)) * (1 + c * b) ≤ 1 := by
    have h1 := Real.add_one_le_exp (c * b)
    have h2 : Real.exp (-(c * b)) * Real.exp (c * b) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-(c * b))]
  have h1 : c * b / (1 + c * b) ≤ 1 - Real.exp (-(c * b)) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  refine le_trans ?_ h1
  rw [Real.sqrt_le_left (by positivity), div_pow, div_le_div_iff₀ (by linarith) (by positivity)]
  -- It remains to see `1 + 2 c b ≤ c² b C`.
  have hkey : 1 + 2 * c * b ≤ c ^ 2 * b * C := by
    have h3 : c ^ 2 * b * (2 / c + 1 / (c ^ 2 * b₀)) = 2 * c * b + b / b₀ := by
      field_simp
    have h4 : 1 ≤ b / b₀ := by rw [le_div_iff₀ hb₀]; linarith
    have h5 : c ^ 2 * b * (2 / c + 1 / (c ^ 2 * b₀)) ≤ c ^ 2 * b * C :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hkey hb0.le]

/-- Scalar part of Final lower bound in `thm:main`: if `c > 0`, `C ≥ 1 / c²` and `b ≥ 0`, then
`√(b / (C + b)) ≤ c √b`. -/
theorem sqrt_div_add_le_mul_sqrt {c C b : ℝ} (hc : 0 < c) (hC : 1 / c ^ 2 ≤ C) (hb : 0 ≤ b) :
    √(b / (C + b)) ≤ c * √b := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  have hcC : 1 ≤ C * c ^ 2 := (div_le_iff₀ hc2).1 hC
  have h1 : b / (C + b) ≤ c ^ 2 * b := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hcC hb, mul_nonneg (mul_nonneg hc2.le hb) hb]
  calc √(b / (C + b)) ≤ √(c ^ 2 * b) := Real.sqrt_le_sqrt h1
    _ = c * √b := by rw [Real.sqrt_mul hc2.le, Real.sqrt_sq hc.le]

/-- Square-root sum estimate: if `∑ⱼ gⱼ = 0` and `0 ≤ 1 + gⱼ ≤ 2` for every `j`, then
`∑ⱼ gⱼ² / (2 n (1 + √2)²) ≤ 1 - (1/n) ∑ⱼ √(1 + gⱼ)`. -/
theorem sum_sq_div_le_one_sub_mean_sqrt {n : ℕ} (g : Fin n → ℝ) (hsum : ∑ j, g j = 0)
    (hg : ∀ j, 0 ≤ 1 + g j ∧ 1 + g j ≤ 2) :
    (∑ j, g j ^ 2) / (2 * n * (1 + √2) ^ 2) ≤ 1 - (∑ j, √(1 + g j)) / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- `gⱼ² ≤ (1 + √2)² (√(1 + gⱼ) - 1)²`.
  have hterm : ∀ j, g j ^ 2 ≤ (1 + √2) ^ 2 * (√(1 + g j) - 1) ^ 2 := by
    intro j
    obtain ⟨h0, h2⟩ := hg j
    have hs := Real.sq_sqrt h0
    have hs0 := Real.sqrt_nonneg (1 + g j)
    have hs2 : √(1 + g j) ≤ √2 := Real.sqrt_le_sqrt h2
    have hge : g j = (√(1 + g j) - 1) * (√(1 + g j) + 1) := by linear_combination -hs
    have hle : (√(1 + g j) + 1) ^ 2 ≤ (1 + √2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc g j ^ 2 = (√(1 + g j) - 1) ^ 2 * (√(1 + g j) + 1) ^ 2 := by
          rw [← mul_pow, ← hge]
      _ ≤ (√(1 + g j) - 1) ^ 2 * (1 + √2) ^ 2 :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = (1 + √2) ^ 2 * (√(1 + g j) - 1) ^ 2 := by ring
  -- `∑ⱼ (√(1 + gⱼ) - 1)² = 2 n - 2 ∑ⱼ √(1 + gⱼ)`, since `∑ⱼ gⱼ = 0`.
  have hsumsq : ∑ j, (√(1 + g j) - 1) ^ 2 = 2 * n - 2 * ∑ j, √(1 + g j) := by
    have h : ∀ j, (√(1 + g j) - 1) ^ 2 = 2 + g j - 2 * √(1 + g j) := by
      intro j
      linear_combination Real.sq_sqrt (hg j).1
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsum2 : ∑ j, g j ^ 2 ≤ (1 + √2) ^ 2 * (2 * n - 2 * ∑ j, √(1 + g j)) := by
    rw [← hsumsq, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hterm j
  rw [div_le_iff₀ (by positivity)]
  have heq : (1 - (∑ j, √(1 + g j)) / n) * (2 * n * (1 + √2) ^ 2) =
      (1 + √2) ^ 2 * (2 * n - 2 * ∑ j, √(1 + g j)) := by
    field_simp
  linarith

/-- `k L / (C n + k L) = b / (C + b)`, with `L = log (k + 1)` and `b = b_{n,k} = k L / n`. -/
theorem div_add_eq_bScale {n k : ℕ} {C : ℝ} (hn : 0 < n) (hC : 0 < C) :
    (k : ℝ) * Real.log ((k : ℝ) + 1) / (C * n + (k : ℝ) * Real.log ((k : ℝ) + 1)) =
      bScale n k / (C + bScale n k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hL : 0 ≤ (k : ℝ) * Real.log ((k : ℝ) + 1) :=
    mul_nonneg hk0 (Real.log_nonneg (by linarith))
  have hden : 0 < C * n + (k : ℝ) * Real.log ((k : ℝ) + 1) := by positivity
  have hden' : 0 < C + (k : ℝ) * Real.log ((k : ℝ) + 1) / n := by positivity
  unfold bScale
  rw [div_eq_div_iff hden.ne' hden'.ne']
  field_simp

end Parking
