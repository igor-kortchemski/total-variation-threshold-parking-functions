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

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Analytic tools for the characteristic function of the log-likelihood ratio

This module collects the analytic facts used in
the proof of `thm:profile` to expand the
characteristic function `E[e^{iuL_{n,k}}] = ((1/n) ∑ⱼ (1 + g_n(j))^{iu})^k`. It depends on
Mathlib only.

* `tendsto_one_add_pow_of_tendsto`: if `zᵢ → 0` and `kᵢ zᵢ → t` along any filter, then
  `(1 + zᵢ)^{kᵢ} → e^t`. Mathlib only has the case `kᵢ = i`
  (`Complex.tendsto_one_add_pow_exp_of_tendsto`). Here `(1 + z)^k = exp (k log (1 + z))` for
  `‖z‖ ≤ 1/2`, and `‖k (log (1 + z) - z)‖ ≤ ‖k z‖ ‖z‖`.
* `abs_log_one_add_le` and `abs_log_one_add_sub_le`: for `e^{-1} ≤ 1 + y`,
  `|log (1 + y)| ≤ e |y|` and `|log (1 + y) - y + y²/2| ≤ e |y|³`. The first follows from
  `1 - 1/x ≤ log x ≤ x - 1`, the second from the mean value inequality on the segment
  `[0, y]`, where the derivative `t² / (1 + t)` is at most `e y²`.
* `exists_norm_cexp_log_sub_le`: the cubic expansion
  `(1 + y)^{iu} = 1 + iuy - (u² + iu) y²/2 + O_u(|y|³)`, uniformly for
  `e^{-1} ≤ 1 + y ≤ 2`.
* `exists_norm_sum_cexp_log_sub_le`: its sum over `j : Fin n`, with a constant that depends
  on `u` only.
-/

public section

open Filter Topology

namespace Parking

/-- If `zᵢ → 0` and `kᵢ zᵢ → t` along a filter, then `(1 + zᵢ)^{kᵢ} → e^t`. The exponents are
arbitrary natural numbers; they need not tend to infinity. -/
theorem tendsto_one_add_pow_of_tendsto {ι : Type*} {l : Filter ι} {z : ι → ℂ} {k : ι → ℕ}
    {t : ℂ} (hz : Tendsto z l (𝓝 0)) (hkz : Tendsto (fun i => (k i : ℂ) * z i) l (𝓝 t)) :
    Tendsto (fun i => (1 + z i) ^ k i) l (𝓝 (Complex.exp t)) := by
  have hsmall : ∀ᶠ i in l, ‖z i‖ < 1 / 2 := by
    have h := hz.norm
    rw [norm_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  have hlog : Tendsto (fun i => (k i : ℂ) * Complex.log (1 + z i)) l (𝓝 t) := by
    have hbound : Tendsto (fun i => ‖(k i : ℂ) * z i‖ * ‖z i‖) l (𝓝 0) := by
      simpa using hkz.norm.mul hz.norm
    have hdiff : Tendsto (fun i => (k i : ℂ) * Complex.log (1 + z i) - (k i : ℂ) * z i) l
        (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hbound
      filter_upwards [hsmall] with i hi
      have h0 : 0 ≤ ‖z i‖ := norm_nonneg _
      have h1 := Complex.norm_log_one_add_sub_self_le (hi.trans (by norm_num))
      have h2 : (1 - ‖z i‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      rw [← mul_sub, norm_mul, norm_mul, mul_assoc]
      gcongr
      calc ‖Complex.log (1 + z i) - z i‖ ≤ ‖z i‖ ^ 2 * (1 - ‖z i‖)⁻¹ / 2 := h1
        _ = ‖z i‖ ^ 2 * ((1 - ‖z i‖)⁻¹ / 2) := by ring
        _ ≤ ‖z i‖ ^ 2 * 1 := by gcongr; linarith
        _ = ‖z i‖ * ‖z i‖ := by ring
    simpa using hdiff.add hkz
  refine ((Complex.continuous_exp.tendsto t).comp hlog).congr' ?_
  filter_upwards [hsmall] with i hi
  have hne : 1 + z i ≠ 0 := by
    intro h
    have hz1 : z i = -1 := by linear_combination h
    rw [hz1] at hi
    norm_num at hi
  simp only [Function.comp_apply]
  rw [Complex.exp_nat_mul, Complex.exp_log hne]

/-- `e · e^{-1} = 1`, in the form used for the bounds below: if `e^{-1} ≤ 1 + t`, then
`1 ≤ e (1 + t)`. -/
theorem one_le_exp_one_mul_of_exp_neg_one_le {t : ℝ} (ht : Real.exp (-1) ≤ 1 + t) :
    1 ≤ Real.exp 1 * (1 + t) := by
  calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; norm_num
    _ ≤ Real.exp 1 * (1 + t) := by gcongr

/-- If `e^{-1} ≤ 1 + y` and `t` lies between `0` and `y`, then `e^{-1} ≤ 1 + t` and
`|t| ≤ |y|`. -/
theorem exp_neg_one_le_one_add_of_mem_uIcc {y t : ℝ} (hy : Real.exp (-1) ≤ 1 + y)
    (ht : t ∈ Set.uIcc 0 y) : Real.exp (-1) ≤ 1 + t ∧ |t| ≤ |y| := by
  refine ⟨?_, by simpa using Set.abs_sub_left_of_mem_uIcc ht⟩
  rcases Set.mem_uIcc.1 ht with ⟨h0, -⟩ | ⟨hyt, -⟩
  · have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    linarith
  · linarith

/-- For `e^{-1} ≤ 1 + y`, `|log (1 + y)| ≤ e |y|`. -/
theorem abs_log_one_add_le {y : ℝ} (hy : Real.exp (-1) ≤ 1 + y) :
    |Real.log (1 + y)| ≤ Real.exp 1 * |y| := by
  have hpos : 0 < 1 + y := (Real.exp_pos _).trans_le hy
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hey := one_le_exp_one_mul_of_exp_neg_one_le hy
  have hup := Real.log_le_sub_one_of_pos hpos
  have hlow := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
  rw [hinv] at hlow
  have hlow' : -(Real.exp 1 * |y|) ≤ y / (1 + y) := by
    rw [le_div_iff₀ hpos]
    nlinarith [mul_nonneg (abs_nonneg y) (sub_nonneg.2 hey), neg_abs_le y]
  rw [abs_le]
  constructor
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.2 he1) (abs_nonneg y), le_abs_self y]

/-- For `e^{-1} ≤ 1 + y`, `|log (1 + y) - y + y²/2| ≤ e |y|³`. The derivative of the left
side, `t² / (1 + t)`, is at most `e y²` between `0` and `y`. -/
theorem abs_log_one_add_sub_le {y : ℝ} (hy : Real.exp (-1) ≤ 1 + y) :
    |Real.log (1 + y) - y + y ^ 2 / 2| ≤ Real.exp 1 * |y| ^ 3 := by
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) (f' := fun t => 1 / (1 + t) - 1 + t)
    (C := Real.exp 1 * y ^ 2) (s := Set.uIcc 0 y) (x := 0) (y := y) ?_ ?_ (convex_uIcc 0 y)
    Set.left_mem_uIcc Set.right_mem_uIcc
  · simp only [Real.norm_eq_abs, add_zero, Real.log_one, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at key
    calc |Real.log (1 + y) - y + y ^ 2 / 2| ≤ Real.exp 1 * y ^ 2 * |y| := key
      _ = Real.exp 1 * |y| ^ 3 := by rw [← sq_abs y]; ring
  · intro t ht
    have hpos : 0 < 1 + t :=
      (Real.exp_pos _).trans_le (exp_neg_one_le_one_add_of_mem_uIcc hy ht).1
    have h := ((((hasDerivAt_id t).const_add 1).log hpos.ne').sub (hasDerivAt_id t)).add
      ((hasDerivAt_pow 2 t).div_const 2)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp
  · intro t ht
    obtain ⟨ht1, ht2⟩ := exp_neg_one_le_one_add_of_mem_uIcc hy ht
    have hpos : 0 < 1 + t := (Real.exp_pos _).trans_le ht1
    have hey := one_le_exp_one_mul_of_exp_neg_one_le ht1
    have heq : 1 / (1 + t) - 1 + t = t ^ 2 / (1 + t) := by field_simp; ring
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
    have hty : t ^ 2 ≤ y ^ 2 := sq_le_sq.2 ht2
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.2 hey), sq_nonneg y]

/-- The sum of the first three terms of the exponential series. -/
theorem sum_range_three_pow_div_factorial (x : ℂ) :
    ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℂ) = 1 + x + x ^ 2 / 2 := by
  simp [Finset.sum_range_succ, Nat.factorial]

/-- The cubic expansion `(1 + y)^{iu} = 1 + iuy - (u² + iu) y²/2 + O_u(|y|³)`, uniformly for
`e^{-1} ≤ 1 + y ≤ 2`. With `ℓ = log (1 + y)` and `θ = uℓ`, the remainder is
`[e^{iθ} - 1 - iθ + θ²/2] + iu (ℓ - y + y²/2) - (u²/2)(ℓ - y)(ℓ + y)`. -/
theorem exists_norm_cexp_log_sub_le (u : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
    Real.exp (-1) ≤ 1 + y → 1 + y ≤ 2 →
    ‖Complex.exp (u * Real.log (1 + y) * Complex.I) -
        (1 + u * y * Complex.I - (u ^ 2 + u * Complex.I) * y ^ 2 / 2)‖ ≤ K * |y| ^ 3 := by
  refine ⟨(|u| * Real.exp 1) ^ 3 * Real.exp (|u| * Real.exp 1) + |u| * Real.exp 1 +
    u ^ 2 / 2 * (Real.exp 1 + 1) ^ 2, by positivity, ?_⟩
  intro y hy1 hy2
  set e := Real.exp 1 with he
  set ℓ := Real.log (1 + y) with hℓ
  have he0 : 0 ≤ e := (Real.exp_pos 1).le
  have hy : |y| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [Real.exp_pos (-1)]
    · linarith
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hℓ1 : |ℓ| ≤ e * |y| := abs_log_one_add_le hy1
  have hℓ3 : |ℓ - y + y ^ 2 / 2| ≤ e * |y| ^ 3 := abs_log_one_add_sub_le hy1
  have hy32 : |y| ^ 3 ≤ |y| ^ 2 := pow_le_pow_of_le_one hy0 hy (by norm_num)
  have hℓm : |ℓ - y| ≤ (e + 1) * |y| ^ 2 := by
    have h1 : |ℓ - y| ≤ |ℓ - y + y ^ 2 / 2| + |y ^ 2 / 2| := by
      calc |ℓ - y| = |(ℓ - y + y ^ 2 / 2) + -(y ^ 2 / 2)| := by ring_nf
        _ ≤ |ℓ - y + y ^ 2 / 2| + |-(y ^ 2 / 2)| := abs_add_le _ _
        _ = |ℓ - y + y ^ 2 / 2| + |y ^ 2 / 2| := by rw [abs_neg]
    have h2 : |y ^ 2 / 2| ≤ |y| ^ 2 := by
      rw [abs_div, abs_pow, abs_two]
      nlinarith [sq_nonneg |y|]
    nlinarith [mul_le_mul_of_nonneg_left hy32 he0]
  have hℓp : |ℓ + y| ≤ (e + 1) * |y| := by
    calc |ℓ + y| ≤ |ℓ| + |y| := abs_add_le _ _
      _ ≤ e * |y| + |y| := by gcongr
      _ = (e + 1) * |y| := by ring
  set θ : ℝ := u * ℓ with hθ
  have hθ1 : |θ| ≤ |u| * e * |y| := by
    rw [hθ, abs_mul, mul_assoc]
    gcongr
  have hθ2 : |θ| ≤ |u| * e := by
    calc |θ| ≤ |u| * e * |y| := hθ1
      _ ≤ |u| * e * 1 := by gcongr
      _ = |u| * e := by ring
  have hdecomp : Complex.exp (u * ℓ * Complex.I) -
        (1 + u * y * Complex.I - (u ^ 2 + u * Complex.I) * y ^ 2 / 2) =
      (Complex.exp ((θ : ℂ) * Complex.I) -
          ∑ m ∈ Finset.range 3, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) +
        ((u * (ℓ - y + y ^ 2 / 2) : ℝ) : ℂ) * Complex.I -
        ((u ^ 2 / 2 * ((ℓ - y) * (ℓ + y)) : ℝ) : ℂ) := by
    rw [sum_range_three_pow_div_factorial, hθ]
    push_cast
    linear_combination ((u : ℂ) ^ 2 * (ℓ : ℂ) ^ 2 / 2) * Complex.I_sq
  rw [hdecomp]
  have hA : ‖Complex.exp ((θ : ℂ) * Complex.I) -
      ∑ m ∈ Finset.range 3, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖ ≤
      (|u| * e) ^ 3 * Real.exp (|u| * e) * |y| ^ 3 := by
    have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((θ : ℂ) * Complex.I) 3
    have hn : ‖(θ : ℂ) * Complex.I‖ = |θ| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [hn] at h
    refine h.trans ?_
    calc |θ| ^ 3 * Real.exp |θ| ≤ (|u| * e * |y|) ^ 3 * Real.exp (|u| * e) := by
          gcongr
      _ = (|u| * e) ^ 3 * Real.exp (|u| * e) * |y| ^ 3 := by ring
  have hB : ‖((u * (ℓ - y + y ^ 2 / 2) : ℝ) : ℂ) * Complex.I‖ ≤ |u| * e * |y| ^ 3 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      mul_assoc]
    gcongr
  have hC : ‖((u ^ 2 / 2 * ((ℓ - y) * (ℓ + y)) : ℝ) : ℂ)‖ ≤
      u ^ 2 / 2 * (e + 1) ^ 2 * |y| ^ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2 / 2)]
    calc u ^ 2 / 2 * (|ℓ - y| * |ℓ + y|) ≤
        u ^ 2 / 2 * ((e + 1) * |y| ^ 2 * ((e + 1) * |y|)) := by gcongr
      _ = u ^ 2 / 2 * (e + 1) ^ 2 * |y| ^ 3 := by ring
  calc _ ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) -
          ∑ m ∈ Finset.range 3, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)‖ +
        ‖((u * (ℓ - y + y ^ 2 / 2) : ℝ) : ℂ) * Complex.I‖ +
        ‖((u ^ 2 / 2 * ((ℓ - y) * (ℓ + y)) : ℝ) : ℂ)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ (|u| * e) ^ 3 * Real.exp (|u| * e) * |y| ^ 3 + |u| * e * |y| ^ 3 +
        u ^ 2 / 2 * (e + 1) ^ 2 * |y| ^ 3 := by gcongr
    _ = ((|u| * e) ^ 3 * Real.exp (|u| * e) + |u| * e + u ^ 2 / 2 * (e + 1) ^ 2) * |y| ^ 3 := by
        ring

/-- The sum over `j : Fin n` of the cubic expansion of `(1 + gⱼ)^{iu}`, uniformly for
`e^{-1} ≤ 1 + gⱼ ≤ 2`: the constant depends on `u` only. -/
theorem exists_norm_sum_cexp_log_sub_le (u : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (g : Fin n → ℝ),
    (∀ j, Real.exp (-1) ≤ 1 + g j ∧ 1 + g j ≤ 2) →
    ‖∑ j, Complex.exp (u * Real.log (1 + g j) * Complex.I) -
        (n + u * (∑ j, g j) * Complex.I - (u ^ 2 + u * Complex.I) / 2 * ∑ j, g j ^ 2)‖ ≤
      K * ∑ j, |g j| ^ 3 := by
  obtain ⟨K, hK, hbound⟩ := exists_norm_cexp_log_sub_le u
  refine ⟨K, hK, fun n g hg => ?_⟩
  have heq : ∑ j, Complex.exp (u * Real.log (1 + g j) * Complex.I) -
      (n + u * (∑ j, g j) * Complex.I - (u ^ 2 + u * Complex.I) / 2 * ∑ j, g j ^ 2) =
      ∑ j, (Complex.exp (u * Real.log (1 + g j) * Complex.I) -
        (1 + u * g j * Complex.I - (u ^ 2 + u * Complex.I) * g j ^ 2 / 2)) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.sum_div]
    push_cast
    ring
  rw [heq, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact hbound (g j) (hg j).1 (hg j).2

end Parking
