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

public import Parking.LikelihoodLaw
import Parking.CharFunExpansion
import Parking.MarginalSquares
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# The Gaussian limit of the log-likelihood ratio

This module follows the proof of `thm:profile`. Let `k_n log n / n → λ`, with `λ` finite. The log-likelihood ratio
`L_{n,k_n} = ∑_r log (1 + g_n(V_r))` under `Q_{n,k_n} = U_n^{⊗k_n}`, whose law is
`Parking.llrLaw n (k n)`, converges in distribution to `σ G - σ²/2`, where `G ~ N(0,1)` and
`σ² = 4λ/π`.

* `tendsto_charFun_llrLaw`: for every `u`, `E[e^{iuL_{n,k_n}}] → e^{-σ²(u² + iu)/2}`, the
  characteristic function of `N(-σ²/2, σ²)`.
* `tendsto_llrLaw`: the laws converge weakly, by Lévy's continuity theorem
  (`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`).
* `tendsto_of_tendsto_comp_succPNat`: Lévy's theorem in Mathlib is stated for sequences indexed
  by `ℕ`; this helper transfers a limit from `m ↦ f (m + 1)` to `f : ℕ+ → X`.

## Proof

By `Parking.charFun_llrLaw`, the characteristic function is `(1 + z_n)^{k_n}`, where
`z_n = S_n/n - 1` and `S_n = ∑_j (1 + g_n(j))^{iu}`. For `n ≥ 2`, the cubic expansion of
`Parking.exists_norm_sum_cexp_log_sub_le`, together with `∑_j g_n(j) = 0` and
`∑_j |g_n(j)|³ ≤ 6000`, gives `S_n - n = -a S₂(n) + E_n` with `a = (u² + iu)/2`,
`S₂(n) = ∑_j g_n(j)²` and `|E_n| ≤ B` for a constant `B` depending on `u` only. Since
`S₂(n) = (4/π) log n + O(1)` and `k_n / n → 0` (because `log n → ∞`), we get
`k_n S₂(n) / n → 4λ/π` and `S₂(n)/n → 0`. Hence `k_n z_n → -a · 4λ/π` and `z_n → 0`, and
`Parking.tendsto_one_add_pow_of_tendsto` concludes.
-/

public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Parking

/-- A sequence indexed by `ℕ+` converges as soon as its reindexing `m ↦ f (m + 1)` along `ℕ`
converges, to the same limit. -/
theorem tendsto_of_tendsto_comp_succPNat {X : Type*} [TopologicalSpace X] {f : ℕ+ → X} {x : X}
    (h : Tendsto (fun m : ℕ => f m.succPNat) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) := by
  have hpred : Tendsto PNat.natPred atTop atTop :=
    tendsto_atTop_atTop_of_monotone PNat.natPred_monotone fun m =>
      ⟨m.succPNat, (Nat.natPred_succPNat m).ge⟩
  simpa only [Function.comp_def, PNat.succPNat_natPred] using h.comp hpred

/-- `Nat.succPNat : ℕ → ℕ+` tends to infinity. -/
theorem tendsto_succPNat_atTop : Tendsto Nat.succPNat atTop atTop :=
  tendsto_atTop_atTop_of_monotone Nat.succPNat_mono fun n =>
    ⟨n.natPred, (PNat.succPNat_natPred n).ge⟩

/-- `(n : ℝ) → ∞` as `n → ∞` in `ℕ+`. -/
theorem tendsto_pnat_cast_atTop : Tendsto (fun n : ℕ+ => (n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop

/-- Eventually `n ≥ 2` in `ℕ+`. -/
theorem eventually_two_le_pnat : ∀ᶠ n : ℕ+ in atTop, 2 ≤ (n : ℕ) :=
  tendsto_PNat_val_atTop_atTop.eventually (eventually_ge_atTop 2)

/-- If `k_n log n / n → λ`, then `k_n / n → 0`, since `log n → ∞`. -/
theorem tendsto_div_of_tendsto_kLogDiv {k : ℕ+ → ℕ} {l : ℝ}
    (hl : Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ+ => (k n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ+ => (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_pnat_cast_atTop)
  have h := hl.mul hlog
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_two_le_pnat] with n hn
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  field_simp

/-- `S₂(n)/n → 0`, where `S₂(n) = ∑_j g_n(j)² = (4/π) log n + O(1)`. -/
theorem tendsto_sum_sq_parkingG_div :
    Tendsto (fun n : ℕ+ => (∑ j, parkingG n j ^ 2) / (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_abs_sum_sq_parkingG_sub_log_le
  have hlogdiv : Tendsto (fun n : ℕ+ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_pnat_cast_atTop
  have hrem : Tendsto (fun n : ℕ+ =>
      (∑ j, parkingG n j ^ 2 - 4 / Real.pi * Real.log (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (Tendsto.div_atTop
      (tendsto_const_nhds : Tendsto (fun _ : ℕ+ => C) atTop (𝓝 C)) tendsto_pnat_cast_atTop)
    filter_upwards [eventually_two_le_pnat] with n hn
    have hpos : (0 : ℝ) < (n : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (hC n hn) hpos.le
  have h := (hlogdiv.const_mul (4 / Real.pi)).add hrem
  rw [mul_zero, add_zero] at h
  refine h.congr fun n => ?_
  ring

/-- If `k_n log n / n → λ`, then `k_n S₂(n) / n → 4λ/π`, where `S₂(n) = ∑_j g_n(j)²`. -/
theorem tendsto_mul_sum_sq_parkingG_div {k : ℕ+ → ℕ} {l : ℝ}
    (hl : Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ+ => (k n : ℝ) * (∑ j, parkingG n j ^ 2) / (n : ℝ)) atTop
      (𝓝 (4 * l / Real.pi)) := by
  obtain ⟨C, hC⟩ := exists_abs_sum_sq_parkingG_sub_log_le
  have hk := tendsto_div_of_tendsto_kLogDiv hl
  have hrem : Tendsto (fun n : ℕ+ => (k n : ℝ) / (n : ℝ) *
      (∑ j, parkingG n j ^ 2 - 4 / Real.pi * Real.log (n : ℝ))) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n : ℕ+ => (k n : ℝ) / (n : ℝ) * C) atTop (𝓝 0) := by
      simpa using hk.mul_const C
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_two_le_pnat] with n hn
    have hnn : (0 : ℝ) ≤ (k n : ℝ) / (n : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (hC n hn) hnn
  have h := (hl.const_mul (4 / Real.pi)).add hrem
  rw [add_zero, show 4 / Real.pi * l = 4 * l / Real.pi by ring] at h
  refine h.congr fun n => ?_
  ring

/-- The cubic expansion of `S_n = ∑_j (1 + g_n(j))^{iu}`: for `n ≥ 2`,
`|S_n - n + (u² + iu)/2 · ∑_j g_n(j)²| ≤ B`, with `B` depending on `u` only. It combines
`Parking.exists_norm_sum_cexp_log_sub_le`, `∑_j g_n(j) = 0` and `∑_j |g_n(j)|³ ≤ 6000`. -/
theorem exists_norm_sum_cexp_parkingG_sub_le (u : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ+,
    2 ≤ (n : ℕ) →
    ‖∑ j : Fin n, Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I) - (n : ℂ) +
        (u ^ 2 + u * Complex.I) / 2 * ((∑ j, parkingG n j ^ 2 : ℝ) : ℂ)‖ ≤ B := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_sum_cexp_log_sub_le u
  refine ⟨K * 6000, by positivity, fun n hn => ?_⟩
  have h := hK n (parkingG n) fun j =>
    ⟨exp_neg_one_le_one_add_parkingG n hn j, one_add_parkingG_le_two n j⟩
  rw [sum_parkingG] at h
  calc _ = ‖∑ j : Fin n, Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I) -
        ((n : ℕ) + u * ((0 : ℝ) : ℂ) * Complex.I -
          (u ^ 2 + u * Complex.I) / 2 * ((∑ j, parkingG n j ^ 2 : ℝ) : ℂ))‖ := by
        congr 1
        push_cast
        ring
    _ ≤ K * ∑ j, |parkingG n j| ^ 3 := h
    _ ≤ K * 6000 := mul_le_mul_of_nonneg_left (sum_abs_parkingG_pow_three_le n hn) hK0

/-- The displayed one-coordinate expansion in `thm:profile`. The constant is chosen
before `n`, so it depends only on `u`, and the error is uniformly `O_u(1/n)`. -/
theorem exists_norm_mean_cexp_parkingG_expansion (u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) →
      ‖(∑ j : Fin n, Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I)) / (n : ℂ) -
        (1 - (2 * (u ^ 2 + u * Complex.I) / Real.pi) *
          ((Real.log (n : ℝ) / (n : ℝ) : ℝ) : ℂ))‖ ≤ B / (n : ℝ) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_sum_cexp_parkingG_sub_le u
  obtain ⟨C, hC⟩ := exists_abs_sum_sq_parkingG_sub_log_le
  let a : ℂ := (u ^ 2 + u * Complex.I) / 2
  refine ⟨B + ‖a‖ * |C|, by positivity, fun n hn => ?_⟩
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have heq :
      (∑ j : Fin n, Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I)) / (n : ℂ) -
        (1 - (2 * (u ^ 2 + u * Complex.I) / Real.pi) *
          ((Real.log (n : ℝ) / (n : ℝ) : ℝ) : ℂ)) =
      ((∑ j : Fin n, Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I)) -
        (n : ℂ) + a * ((∑ j, parkingG n j ^ 2 : ℝ) : ℂ) -
        a * ((∑ j, parkingG n j ^ 2 - 4 / Real.pi * Real.log (n : ℝ) : ℝ) : ℂ)) /
        (n : ℂ) := by
    generalize (∑ j : Fin n, Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I)) = S
    dsimp [a]
    push_cast
    field_simp
    ring
  rw [heq, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc _ ≤ ‖(∑ j : Fin n, Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I)) -
          (n : ℂ) + a * ((∑ j, parkingG n j ^ 2 : ℝ) : ℂ)‖ +
        ‖a * ((∑ j, parkingG n j ^ 2 - 4 / Real.pi * Real.log (n : ℝ) : ℝ) : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ B + ‖a‖ * |C| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (hB n hn)
        (mul_le_mul_of_nonneg_left ((hC n hn).trans (le_abs_self C)) (norm_nonneg a))

/-- Characteristic-function limit (`thm:profile`): use the uniform `O_u(1/n)` expansion,
`k_n log n/n → l`, `k_n/n → 0`, and the complex-power limit. -/
theorem tendsto_charFun_llrLaw (k : ℕ+ → ℕ) (l : ℝ)
    (hl : Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 l)) (u : ℝ) :
    Tendsto (fun n : ℕ+ => charFun (llrLaw n (k n) : Measure ℝ) u) atTop
      (𝓝 (charFun (gaussianReal (-(2 * l / Real.pi)) (4 * l / Real.pi).toNNReal) u)) := by
  have hl0 : 0 ≤ l := ge_of_tendsto' hl (kLogDiv_nonneg k)
  obtain ⟨B, hB0, hB⟩ := exists_norm_mean_cexp_parkingG_expansion u
  set a : ℂ := 2 * (u ^ 2 + u * Complex.I) / Real.pi with ha
  set S : ℕ+ → ℂ := fun n =>
    (∑ j : Fin n, Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I)) / (n : ℂ)
  set R : ℕ+ → ℂ := fun n => S n - (1 - a * ((Real.log (n : ℝ) / (n : ℝ) : ℝ) : ℂ)) with hR
  have hRB : ∀ᶠ n : ℕ+ in atTop, ‖R n‖ ≤ B / (n : ℝ) := by
    filter_upwards [eventually_two_le_pnat] with n hn
    exact hB n hn
  have hR0 : Tendsto R atTop (𝓝 0) := by
    exact squeeze_zero_norm' hRB (Tendsto.div_atTop tendsto_const_nhds tendsto_pnat_cast_atTop)
  have hlogdiv : Tendsto (fun n : ℕ+ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_pnat_cast_atTop
  have hz : Tendsto (fun n : ℕ+ => S n - 1) atTop (𝓝 0) := by
    have h := hR0.sub (hlogdiv.ofReal.const_mul a)
    rw [Complex.ofReal_zero, mul_zero, sub_zero] at h
    refine h.congr fun n => ?_
    rw [hR]
    ring
  have hkR : Tendsto (fun n : ℕ+ => (k n : ℂ) * R n) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n : ℕ+ => (k n : ℝ) / (n : ℝ) * B) atTop (𝓝 0) := by
      simpa using (tendsto_div_of_tendsto_kLogDiv hl).mul_const B
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hRB] with n hn
    rw [norm_mul, Complex.norm_natCast]
    calc (k n : ℝ) * ‖R n‖ ≤ (k n : ℝ) * (B / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
      _ = (k n : ℝ) / (n : ℝ) * B := by ring
  have hkz : Tendsto (fun n : ℕ+ => (k n : ℂ) * (S n - 1)) atTop
      (𝓝 (0 - a * (l : ℂ))) := by
    have h := hkR.sub (hl.ofReal.const_mul a)
    refine h.congr fun n => ?_
    rw [hR]
    push_cast
    ring
  have hlim := tendsto_one_add_pow_of_tendsto hz hkz
  rw [charFun_gaussianReal, Real.coe_toNNReal _ (by positivity)]
  convert hlim using 2 with n
  · rw [charFun_llrLaw]
    dsimp [S]
    ring
  · rw [ha]
    congr 1
    push_cast
    ring

/-- Weak convergence (`thm:profile`): if `k_n log n / n → λ` with `λ` finite, the law
of `L_{n,k_n}` converges weakly to `N(-σ²/2, σ²)`, `σ² = 4λ/π`, the law of `σ G - σ²/2`. -/
theorem tendsto_llrLaw (k : ℕ+ → ℕ) (l : ℝ)
    (hl : Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ+ => llrLaw n (k n)) atTop
      (𝓝 ⟨gaussianReal (-(2 * l / Real.pi)) (4 * l / Real.pi).toNNReal, inferInstance⟩) := by
  refine tendsto_of_tendsto_comp_succPNat
    (ProbabilityMeasure.tendsto_of_tendsto_charFun fun u => ?_)
  exact (tendsto_charFun_llrLaw k l hl u).comp tendsto_succPNat_atTop

end Parking
