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

public import Parking.MainScalar
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The logarithmic scalar route in the manuscript

These are the scalar steps of `eq:tv_decoupling` and its uses in the upper and
small-scale lower bounds. The function `b log(e/b)` is used with its actual
limit at zero; no power-law replacement enters this route.
-/

public section

open Filter Topology

namespace Parking

/-- The identity underlying the continuous extension of `b log(e/b)` at zero. -/
theorem mul_log_exp_div (b : ℝ) :
    b * Real.log (Real.exp 1 / b) = b - b * Real.log b := by
  by_cases hb : b = 0
  · simp [hb]
  · rw [Real.log_div (Real.exp_ne_zero _) hb, Real.log_exp]
    ring

/-- The scalar inequality used immediately after `eq:tv_decoupling`. -/
theorem mul_log_exp_div_le_one {b : ℝ} (hb : 0 ≤ b) :
    b * Real.log (Real.exp 1 / b) ≤ 1 := by
  rw [mul_log_exp_div]
  linarith [Real.self_sub_one_le_mul_log hb]

/-- The logarithmic error vanishes at zero, as used in the small-scale lower bound. -/
theorem tendsto_mul_log_exp_div_zero :
    Tendsto (fun b : ℝ => b * Real.log (Real.exp 1 / b)) (𝓝 0) (𝓝 0) := by
  have h : Continuous (fun b : ℝ => b - b * Real.log b) :=
    continuous_id.sub Real.continuous_mul_log
  simpa only [mul_log_exp_div, zero_mul, sub_zero] using h.tendsto (0 : ℝ)

/-- An explicit quantifier form of the preceding limit, with one threshold valid for
all `0 < b ≤ b₀`. -/
theorem exists_small_mul_log_exp_div {ε : ℝ} (hε : 0 < ε) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ b₀ < 1 ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
      b * Real.log (Real.exp 1 / b) ≤ ε := by
  obtain ⟨δ, hδ, hbound⟩ := Metric.tendsto_nhds_nhds.1 tendsto_mul_log_exp_div_zero ε hε
  refine ⟨min (1 / 2) (δ / 2), lt_min (by norm_num) (half_pos hδ),
    (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro b hb hb₀
  have hbδ : |b| < δ := by
    rw [abs_of_pos hb]
    linarith [hb₀.trans (min_le_right _ _)]
  have h := hbound (by simpa only [Real.dist_eq, sub_zero] using hbδ)
  rw [Real.dist_eq, sub_zero] at h
  exact (le_abs_self _).trans h.le

/-- For `0 < b ≤ 1`, the logarithm in the manuscript's estimate is at least one. -/
theorem one_le_log_exp_div {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    1 ≤ Real.log (Real.exp 1 / b) := by
  rw [Real.log_div (Real.exp_ne_zero _) hb.ne', Real.log_exp]
  linarith [Real.log_nonpos hb.le hb1]

/-- The identity `n = k log(k+1)/b` gives the manuscript's logarithmic estimate. -/
theorem log_le_two_log_add_one_add_log_inv {n k : ℕ}
    (hn : 0 < n) (hk : 1 ≤ k) :
    Real.log n ≤ 2 * Real.log ((k : ℝ) + 1) + Real.log (1 / bScale n k) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hL : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
  have hb : 0 < bScale n k := bScale_pos hn hk
  have heq : Real.log (n : ℝ) = Real.log (k : ℝ) + Real.log (Real.log ((k : ℝ) + 1)) -
      Real.log (bScale n k) := by
    rw [bScale, Real.log_div (mul_pos hk0 hL).ne' hn0.ne',
      Real.log_mul hk0.ne' hL.ne']
    ring
  have hlogk : Real.log (k : ℝ) ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log hk0 (by linarith)
  have hlogL : Real.log (Real.log ((k : ℝ) + 1)) ≤ Real.log ((k : ℝ) + 1) :=
    (Real.log_le_sub_one_of_pos hL).trans (by linarith)
  rw [Real.log_div one_ne_zero hb.ne', Real.log_one]
  linarith

/-- The second scalar inequality of `eq:tv_decoupling`, with the absolute constant `2`.
The statement is uniform in `n,k` and uses exactly `0 < b < 1`. -/
theorem mul_sqrt_log_le_two_bScale_sqrt_log {n k : ℕ}
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hb1 : bScale n k < 1) :
    (k : ℝ) / n * √(Real.log n) ≤
      2 * bScale n k * √(Real.log (Real.exp 1 / bScale n k)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hL0 : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
  have hLhalf : (1 / 2 : ℝ) ≤ Real.log ((k : ℝ) + 1) := by
    have h2k : (2 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (by omega : 2 ≤ k + 1)
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2k
    have h2 := Real.log_two_gt_d9
    linarith
  have hb0 : 0 < bScale n k := bScale_pos (by omega) hk
  have ht : 0 ≤ Real.log (1 / bScale n k) := Real.log_nonneg (by
    rw [le_div_iff₀ hb0]
    linarith)
  have hlog : Real.log n ≤ 2 * Real.log ((k : ℝ) + 1) + Real.log (1 / bScale n k) :=
    log_le_two_log_add_one_add_log_inv (by omega) hk
  have hE : Real.log (Real.exp 1 / bScale n k) = 1 + Real.log (1 / bScale n k) := by
    rw [Real.log_div (Real.exp_ne_zero _) hb0.ne', Real.log_exp,
      Real.log_div one_ne_zero hb0.ne', Real.log_one]
    ring
  have hE0 : 0 ≤ Real.log (Real.exp 1 / bScale n k) := by rw [hE]; linarith
  have hLsq : 2 * Real.log ((k : ℝ) + 1) ≤ 4 * Real.log ((k : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (Real.log ((k : ℝ) + 1) - 1 / 2)]
  have hLsq1 : 1 ≤ 4 * Real.log ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hs : √(Real.log n) ≤
      2 * Real.log ((k : ℝ) + 1) * √(Real.log (Real.exp 1 / bScale n k)) := by
    apply (Real.sqrt_le_left (by positivity)).2
    rw [mul_pow, mul_pow, Real.sq_sqrt hE0, hE]
    nlinarith [mul_le_mul_of_nonneg_right hLsq1 ht]
  calc (k : ℝ) / n * √(Real.log n) ≤
      (k : ℝ) / n * (2 * Real.log ((k : ℝ) + 1) *
        √(Real.log (Real.exp 1 / bScale n k))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 2 * bScale n k * √(Real.log (Real.exp 1 / bScale n k)) := by
      unfold bScale
      ring

/-- The first scalar inequality of `eq:tv_decoupling`, reducing the Pinsker bound. -/
theorem sqrt_decoupling_le_mul_sqrt_log {n k : ℕ} (hn : 2 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    √((k : ℝ) * ((k : ℝ) - 1) * Real.log n / (2 * n * ((n : ℝ) - 1))) ≤
      (k : ℝ) / n * √(Real.log n) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by linarith
  have hnm : 0 < (n : ℝ) - 1 := by linarith
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  apply (Real.sqrt_le_left (by positivity)).2
  rw [mul_pow, div_pow, Real.sq_sqrt hlog]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hbase : (k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ 2 ≤
      (k : ℝ) ^ 2 * (2 * n * ((n : ℝ) - 1)) := by
    have h1 : (k : ℝ) - 1 ≤ k := by linarith
    have h2 : (n : ℝ) ≤ 2 * ((n : ℝ) - 1) := by linarith
    calc (k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * n ^ 2 := by
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k * n ^ 2) (sub_nonneg.2 h1)]
      _ ≤ (k : ℝ) ^ 2 * (2 * n * ((n : ℝ) - 1)) := by
          nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ k ^ 2 * n)]
  nlinarith [mul_le_mul_of_nonneg_right hbase hlog]

/-- The error is `√b` times a factor tending to zero, as needed for the lower bound. -/
theorem b_mul_sqrt_log_exp_div {b : ℝ} (hb : 0 ≤ b) :
    b * √(Real.log (Real.exp 1 / b)) =
      √b * √(b * Real.log (Real.exp 1 / b)) := by
  rw [Real.sqrt_mul hb, ← mul_assoc, Real.mul_self_sqrt hb]

/-- The upper-bound use of `b log(e/b) ≤ 1`. -/
theorem b_mul_sqrt_log_exp_div_le_sqrt {b : ℝ} (hb : 0 ≤ b) :
    b * √(Real.log (Real.exp 1 / b)) ≤ √b := by
  rw [b_mul_sqrt_log_exp_div hb]
  calc √b * √(b * Real.log (Real.exp 1 / b)) ≤ √b * 1 := by
        gcongr
        exact Real.sqrt_le_one.2 (mul_log_exp_div_le_one hb)
    _ = √b := mul_one _

end Parking
