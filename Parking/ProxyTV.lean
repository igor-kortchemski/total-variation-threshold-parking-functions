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

public import Parking.ProductScore
import Parking.ScoreTV
import Parking.Symmetrization

/-!
# Comparison of the score norm with the proxy, and the proof of `AKVZ26.ProductTV`

This module compares the score norm
`A = 𝔼 (∑_r U_r²)^{1/2}` (`akvzScoreNorm`) with `s` and `K = k Ψ(s)`, where `Ψ` is the proxy
`akvzProxy`, and combines the comparison with [AKVZ26, Theorem 1.1]
(`tvDist_pi_comparable_scoreNorm`) to prove `AKVZ26.ProductTV`.

This elementary comparison proves the finite identical-factor specialization of
[AKVZ26, Theorem 1.2] using [AKVZ26, Theorem 1.1], without invoking Latała's theorem.

Notation: `M = (P + Q) / 2`, `u` the AKVZ score, `U_r = u(X_r)` for `X_1, …, X_k` independent
of law `M`, `V_r = U_r² / s²`, and
`K = k Ψ(s) = ∑_r 𝔼 min (V_r, √V_r)`. The comparison lemmas hold for an arbitrary probability
weight `M` and an arbitrary function `u` (neither `|u| ≤ 1` nor centring is used).

* Upper bound (`akvzScoreNorm_le`): `A ≤ s (√K + K)`, from the pointwise truncation at level
  `s` (`sqrt_sum_sq_le_proxy`) and Jensen's inequality for the square root
  (`sum_mul_sqrt_le_sqrt_sum_mul`).
* Lower bound (`le_akvzScoreNorm`, `exists_le_akvzScoreNorm`): `A ≥ s min(1, K) / 5`. Put
  `m = min(1, K)`, `w = min(|u| / s, 1)` and `y = 𝔼 w²`.
  * If `k y ≥ m / 2`: `A ≥ s (1 - e^{-k y / 2}) ≥ s m / 5`, by step 3 of
    `Parking.ProductScore` applied to `w` (`one_sub_exp_le_sum_prod_mul_sqrt`).
  * Otherwise, with `p = ℙ(|U| > s)` and `Z = 𝔼 |U| 1_{|U| > s}`: `k p ≤ k y < 1/2`, and
    `K ≤ k Z / s + k y` gives `k Z ≥ s m / 2`. Pointwise,
    `(∑_r U_r²)^{1/2} ≥ ∑_r Z_r ∏_{r' ≠ r} 1_{|U_{r'}| ≤ s}` (`sum_prod_ite_le`); taking
    expectations and using Bernoulli's inequality, `A ≥ k Z (1 - p)^k ≥ k Z (1 - k p) ≥ s m / 4`.
* Assembly (`akvz26_productTV`): with `c₁ ≤ K ≤ C₁`, `min(1, c₁) s / 5 ≤ A ≤ (√C₁ + C₁) s`, and
  `tvDist_pi_comparable_scoreNorm` gives `AKVZ26.ProductTV` with `c = min(1, c₁) / 1005` and
  `C = 201 max(1, √C₁ + C₁)`.
-/

public section

open MeasureTheory

namespace Parking

/-! ### Elementary inequalities -/

/-- `√(x + y) ≤ √x + √y` for `x, y ≥ 0`. -/
theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- The proxy term above level `s`: if `s < |t|`, then
`min (t² / s², |t| / s) = |t| / s`. -/
theorem min_sq_div_eq_of_lt {s t : ℝ} (hs : 0 < s) (h : s < |t|) :
    min (t ^ 2 / s ^ 2) (|t| / s) = |t| / s := by
  have h1 : 1 < |t| / s := (one_lt_div hs).2 h
  have e : t ^ 2 / s ^ 2 = (|t| / s) ^ 2 := by rw [div_pow, sq_abs]
  rw [e]
  exact min_eq_right (by nlinarith)

/-- The proxy term below level `s`: if `|t| ≤ s`, then
`min (t² / s², |t| / s) = t² / s²`. -/
theorem min_sq_div_eq_of_le {s t : ℝ} (hs : 0 < s) (h : |t| ≤ s) :
    min (t ^ 2 / s ^ 2) (|t| / s) = t ^ 2 / s ^ 2 := by
  have h1 : |t| / s ≤ 1 := (div_le_one hs).2 h
  have h0 : 0 ≤ |t| / s := div_nonneg (abs_nonneg t) hs.le
  have e : t ^ 2 / s ^ 2 = (|t| / s) ^ 2 := by rw [div_pow, sq_abs]
  rw [e]
  exact min_eq_left (by nlinarith)

/-- **Truncation at level `s`**, pointwise: for `s > 0`,
`√(∑ᵢ vᵢ²) ≤ s (√(∑ᵢ mᵢ) + ∑ᵢ mᵢ)` with `mᵢ = min (vᵢ² / s², |vᵢ| / s)`. It splits
`vᵢ² = vᵢ² 1_{|vᵢ| ≤ s} + vᵢ² 1_{|vᵢ| > s}` and uses `√(x + y) ≤ √x + √y` and
`‖·‖₂ ≤ ‖·‖₁` on the second part. -/
theorem sqrt_sum_sq_le_proxy {ι : Type*} (t : Finset ι) (v : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    √(∑ i ∈ t, v i ^ 2) ≤
      s * (√(∑ i ∈ t, min (v i ^ 2 / s ^ 2) (|v i| / s)) +
        ∑ i ∈ t, min (v i ^ 2 / s ^ 2) (|v i| / s)) := by
  classical
  have hs' : s ≠ 0 := hs.ne'
  have hm0 : ∀ i, 0 ≤ min (v i ^ 2 / s ^ 2) (|v i| / s) := fun i =>
    le_min (by positivity) (div_nonneg (abs_nonneg _) hs.le)
  let p : ι → ℝ := fun i => if s < |v i| then 0 else v i ^ 2
  let q : ι → ℝ := fun i => if s < |v i| then |v i| else 0
  have hpq : ∀ i, v i ^ 2 = p i + q i ^ 2 := by
    intro i
    by_cases h : s < |v i|
    · simp [p, q, h, sq_abs]
    · simp [p, q, h]
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    by_cases h : s < |v i|
    · simp [p, h]
    · simp only [p, h, ↓reduceIte]
      positivity
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i
    by_cases h : s < |v i|
    · simp [q, h]
    · simp [q, h]
  have hp : ∀ i, p i ≤ s ^ 2 * min (v i ^ 2 / s ^ 2) (|v i| / s) := by
    intro i
    by_cases h : s < |v i|
    · simp only [p, h, ↓reduceIte]
      exact mul_nonneg (sq_nonneg s) (hm0 i)
    · simp only [p, h, ↓reduceIte]
      rw [min_sq_div_eq_of_le hs (not_lt.1 h)]
      field_simp
      exact le_rfl
  have hq : ∀ i, q i ≤ s * min (v i ^ 2 / s ^ 2) (|v i| / s) := by
    intro i
    by_cases h : s < |v i|
    · simp only [q, h, ↓reduceIte]
      rw [min_sq_div_eq_of_lt hs h]
      field_simp
      exact le_rfl
    · simp only [q, h, ↓reduceIte]
      exact mul_nonneg hs.le (hm0 i)
  calc √(∑ i ∈ t, v i ^ 2) = √(∑ i ∈ t, p i + ∑ i ∈ t, q i ^ 2) := by
        rw [← Finset.sum_add_distrib]
        exact congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => hpq i)
    _ ≤ √(∑ i ∈ t, p i) + √(∑ i ∈ t, q i ^ 2) :=
        sqrt_add_le_add_sqrt (Finset.sum_nonneg fun i _ => hp0 i)
          (Finset.sum_nonneg fun i _ => sq_nonneg _)
    _ ≤ √(s ^ 2 * ∑ i ∈ t, min (v i ^ 2 / s ^ 2) (|v i| / s)) + ∑ i ∈ t, q i := by
        refine add_le_add (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_iff.2
          ⟨Finset.sum_nonneg fun i _ => hq0 i,
            Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hq0 i⟩)
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => hp i
    _ ≤ s * √(∑ i ∈ t, min (v i ^ 2 / s ^ 2) (|v i| / s)) +
          s * ∑ i ∈ t, min (v i ^ 2 / s ^ 2) (|v i| / s) := by
        rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
        refine add_le_add le_rfl ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => hq i
    _ = s * (√(∑ i ∈ t, min (v i ^ 2 / s ^ 2) (|v i| / s)) +
          ∑ i ∈ t, min (v i ^ 2 / s ^ 2) (|v i| / s)) := by ring

/-- **Jensen's inequality for the square root** under probability weights:
`∑ᵢ wᵢ √Yᵢ ≤ √(∑ᵢ wᵢ Yᵢ)` when `w ≥ 0`, `∑ᵢ wᵢ = 1` and `Y ≥ 0`. -/
theorem sum_mul_sqrt_le_sqrt_sum_mul {ι : Type*} (t : Finset ι) (w Y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1) (hY : ∀ i, 0 ≤ Y i) :
    ∑ i ∈ t, w i * √(Y i) ≤ √(∑ i ∈ t, w i * Y i) := by
  have e1 : ∑ i ∈ t, w i * √(Y i) = ∑ i ∈ t, w i * |√(Y i)| :=
    Finset.sum_congr rfl fun i _ => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have e2 : ∑ i ∈ t, w i * Y i = ∑ i ∈ t, w i * √(Y i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [Real.sq_sqrt (hY i)]
  rw [e1, e2]
  exact sum_mul_abs_le_sqrt_sum_mul_sq t w (fun i => √(Y i)) hw hw1

/-- Expectation of a sum over the coordinates under a product probability weight:
`∑ x, (∏ r, M (x r)) ∑ r, f (x r) = k ∑ a, M a f a` when `∑ a, M a = 1`. -/
theorem sum_prod_mul_sum_apply {α : Type*} [Fintype α] (M f : α → ℝ) (hM1 : ∑ a, M a = 1)
    (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * ∑ r, f (x r) = k * ∑ a, M a * f a := by
  have h := sum_prod_mul_prod_mul_sum M (fun _ => 1) f (by simpa using hM1) k
  simpa using h

/-! ### Upper bound: `A ≤ s (√K + K)` -/

/-- **Upper comparison with the proxy**, for an arbitrary probability weight `M` and an
arbitrary function `u`: for `s > 0`, `𝔼 (∑_r U_r²)^{1/2} ≤ s (√K + K)` with
`K = k ∑ a, M a min (u a² / s², |u a| / s)`. -/
theorem sum_prod_mul_sqrt_le_proxy {α : Type*} [Fintype α] (M u : α → ℝ) (hM : ∀ a, 0 ≤ M a)
    (hM1 : ∑ a, M a = 1) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) ≤
      s * (√(k * ∑ a, M a * min (u a ^ 2 / s ^ 2) (|u a| / s)) +
        k * ∑ a, M a * min (u a ^ 2 / s ^ 2) (|u a| / s)) := by
  have hW : ∀ x : Fin k → α, 0 ≤ ∏ r, M (x r) := fun x => Finset.prod_nonneg fun r _ => hM _
  have hE := sum_prod_mul_sum_apply M (fun a => min (u a ^ 2 / s ^ 2) (|u a| / s)) hM1 k
  have hJ := sum_mul_sqrt_le_sqrt_sum_mul Finset.univ (fun x : Fin k → α => ∏ r, M (x r))
    (fun x => ∑ r, min (u (x r) ^ 2 / s ^ 2) (|u (x r)| / s)) hW (sum_prod_eq_one M hM1 k)
    (fun x => Finset.sum_nonneg fun r _ =>
      le_min (by positivity) (div_nonneg (abs_nonneg _) hs.le))
  rw [hE] at hJ
  calc ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2)
      ≤ ∑ x : Fin k → α, (∏ r, M (x r)) *
          (s * (√(∑ r, min (u (x r) ^ 2 / s ^ 2) (|u (x r)| / s)) +
            ∑ r, min (u (x r) ^ 2 / s ^ 2) (|u (x r)| / s))) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (sqrt_sum_sq_le_proxy Finset.univ (fun r => u (x r)) hs) (hW x)
    _ = s * (∑ x : Fin k → α, (∏ r, M (x r)) *
            √(∑ r, min (u (x r) ^ 2 / s ^ 2) (|u (x r)| / s)) +
          ∑ x : Fin k → α, (∏ r, M (x r)) *
            ∑ r, min (u (x r) ^ 2 / s ^ 2) (|u (x r)| / s)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ s * (√(k * ∑ a, M a * min (u a ^ 2 / s ^ 2) (|u a| / s)) +
          k * ∑ a, M a * min (u a ^ 2 / s ^ 2) (|u a| / s)) := by
        rw [hE]
        exact mul_le_mul_of_nonneg_left (add_le_add hJ le_rfl) hs.le

/-! ### Lower bound: `A ≥ s min(1, K) / 5` -/

/-- **Pointwise bound with one exceptional coordinate**. Let `Z r ≥ 0` and `B r ∈ {0, 1}`,
with `Z r = 0` whenever `B r = 0`, and `Z r ≤ T` for every `r`. Then
`∑_r Z_r ∏_{r' ≠ r} (1 - B_{r'}) ≤ T`, written as
`∑ r, ∏ r', (if r' = r then Z r' else 1 - B r') ≤ T`: the sum has at most one nonzero term,
and it is at most `Z r ≤ T`. -/
theorem sum_prod_ite_le {k : ℕ} (Z B : Fin k → ℝ) (T : ℝ) (hZ : ∀ r, 0 ≤ Z r)
    (hB : ∀ r, B r = 0 ∨ B r = 1) (hZB : ∀ r, B r = 0 → Z r = 0) (hZT : ∀ r, Z r ≤ T)
    (hT : 0 ≤ T) :
    ∑ r, ∏ r', (if r' = r then Z r' else 1 - B r') ≤ T := by
  have hB1 : ∀ r, 0 ≤ 1 - B r ∧ 1 - B r ≤ 1 := fun r => by
    rcases hB r with h | h <;> simp [h]
  by_cases h : ∃ r0, B r0 = 1
  · obtain ⟨r0, hr0⟩ := h
    rw [Finset.sum_eq_single r0]
    · calc ∏ r', (if r' = r0 then Z r' else 1 - B r')
          ≤ ∏ r', (if r' = r0 then Z r' else 1) := by
            refine Finset.prod_le_prod₀ (fun r' _ => ?_) (fun r' _ => ?_)
            · split_ifs
              · exact hZ r'
              · exact (hB1 r').1
            · split_ifs
              · exact le_rfl
              · exact (hB1 r').2
        _ = Z r0 := by simp
        _ ≤ T := hZT r0
    · intro r _ hr
      refine Finset.prod_eq_zero (Finset.mem_univ r0) ?_
      have hne : ¬ r0 = r := fun h => hr h.symm
      simp [hne, hr0]
    · intro h
      exact absurd (Finset.mem_univ r0) h
  · simp only [not_exists] at h
    have hB0 : ∀ r, B r = 0 := fun r => (hB r).resolve_right (h r)
    calc ∑ r, ∏ r', (if r' = r then Z r' else 1 - B r') = ∑ _r : Fin k, (0 : ℝ) :=
          Finset.sum_congr rfl fun r _ =>
            Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hZB r (hB0 r)])
      _ = 0 := Finset.sum_const_zero
      _ ≤ T := hT

/-- **Lower comparison with the proxy**, for an arbitrary probability weight `M` and an
arbitrary function `u`: for `s > 0`,
`s min(1, K) / 5 ≤ 𝔼 (∑_r U_r²)^{1/2}` with `K = k ∑ a, M a min (u a² / s², |u a| / s)`. -/
theorem le_sum_prod_mul_sqrt_proxy {α : Type*} [Fintype α] (M u : α → ℝ) (hM : ∀ a, 0 ≤ M a)
    (hM1 : ∑ a, M a = 1) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    1 / 5 * s * min 1 (k * ∑ a, M a * min (u a ^ 2 / s ^ 2) (|u a| / s)) ≤
      ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) := by
  classical
  have hs' : s ≠ 0 := hs.ne'
  have hW : ∀ x : Fin k → α, 0 ≤ ∏ r, M (x r) := fun x => Finset.prod_nonneg fun r _ => hM _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set Ψ := ∑ a, M a * min (u a ^ 2 / s ^ 2) (|u a| / s) with hΨ
  set A := ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) with hA
  have hΨ0 : 0 ≤ Ψ := Finset.sum_nonneg fun a _ =>
    mul_nonneg (hM a) (le_min (by positivity) (div_nonneg (abs_nonneg _) hs.le))
  set m := min 1 ((k : ℝ) * Ψ) with hm
  have hm0 : 0 ≤ m := le_min zero_le_one (mul_nonneg hk0 hΨ0)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmK : m ≤ k * Ψ := min_le_right _ _
  -- The truncated score `w = min(|u| / s, 1)`.
  set w : α → ℝ := fun a => min (|u a| / s) 1 with hw
  have hw0 : ∀ a, 0 ≤ w a := fun a => le_min (div_nonneg (abs_nonneg _) hs.le) zero_le_one
  have hw1 : ∀ a, w a ≤ 1 := fun a => min_le_right _ _
  have hsw : ∀ a, s * w a ≤ |u a| := fun a => by
    calc s * w a ≤ s * (|u a| / s) := mul_le_mul_of_nonneg_left (min_le_left _ _) hs.le
      _ = |u a| := by field_simp
  set y := ∑ a, M a * w a ^ 2 with hy
  rcases le_or_gt (m / 2) (k * y) with hcase | hcase
  · -- Case 1: `k y ≥ m / 2`.
    have h1 : 1 - Real.exp (-(k * y) / 2) ≤
        ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, w (x r) ^ 2) :=
      one_sub_exp_le_sum_prod_mul_sqrt M w hM hM1
        (fun a => abs_le.2 ⟨by linarith [hw0 a], hw1 a⟩) k
    have hpt : ∀ x : Fin k → α, s * √(∑ r, w (x r) ^ 2) ≤ √(∑ r, u (x r) ^ 2) := by
      intro x
      rw [← Real.sqrt_sq hs.le, ← Real.sqrt_mul (sq_nonneg s)]
      apply Real.sqrt_le_sqrt
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [← mul_pow, ← sq_abs (u (x r))]
      exact pow_le_pow_left₀ (mul_nonneg hs.le (hw0 _)) (hsw _) 2
    have h2 : s * ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, w (x r) ^ 2) ≤ A := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => by
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left (hpt x) (hW x)
    have h3 : m / 5 ≤ 1 - Real.exp (-(k * y) / 2) := by
      have h4 := div_one_add_le_one_sub_exp_neg (t := m / 4) (by positivity)
      have h5 : Real.exp (-(k * y) / 2) ≤ Real.exp (-(m / 4)) :=
        Real.exp_le_exp.2 (by linarith)
      have h6 : m / 5 ≤ m / 4 / (1 + m / 4) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    calc 1 / 5 * s * m = s * (m / 5) := by ring
      _ ≤ s * (1 - Real.exp (-(k * y) / 2)) := mul_le_mul_of_nonneg_left h3 hs.le
      _ ≤ s * ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, w (x r) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hs.le
      _ ≤ A := h2
  · -- Case 2: `k y < m / 2`, so coordinates above level `s` are rare: `k p < 1/2`.
    set b : α → ℝ := fun a => if s < |u a| then 1 else 0 with hb
    set z : α → ℝ := fun a => if s < |u a| then |u a| else 0 with hz
    have hb01 : ∀ a, b a = 0 ∨ b a = 1 := fun a => by
      by_cases h : s < |u a|
      · right; simp [hb, h]
      · left; simp [hb, h]
    have hb0 : ∀ a, 0 ≤ b a := fun a => by rcases hb01 a with h | h <;> simp [h]
    have hb1 : ∀ a, b a ≤ 1 := fun a => by rcases hb01 a with h | h <;> simp [h]
    have hbw : ∀ a, b a ≤ w a ^ 2 := fun a => by
      by_cases h : s < |u a|
      · have hwa : w a = 1 := min_eq_right ((one_lt_div hs).2 h).le
        simp [hb, h, hwa]
      · have hba : b a = 0 := by simp [hb, h]
        rw [hba]
        exact sq_nonneg _
    have hz0 : ∀ a, 0 ≤ z a := fun a => by
      by_cases h : s < |u a|
      · simp [hz, h]
      · simp [hz, h]
    have hzb : ∀ a, b a = 0 → z a = 0 := fun a hba => by
      by_cases h : s < |u a|
      · simp [hb, h] at hba
      · simp [hz, h]
    have hterm : ∀ a, min (u a ^ 2 / s ^ 2) (|u a| / s) ≤ z a / s + w a ^ 2 := fun a => by
      by_cases h : s < |u a|
      · have hza : z a = |u a| := by simp [hz, h]
        rw [hza]
        exact (min_le_right _ _).trans (le_add_of_nonneg_right (sq_nonneg _))
      · have hza : z a = 0 := by simp [hz, h]
        have hwa : w a = |u a| / s := min_eq_left ((div_le_one hs).2 (not_lt.1 h))
        rw [hza, hwa, zero_div, zero_add, div_pow, sq_abs]
        exact min_le_left _ _
    set p := ∑ a, M a * b a with hp
    set Z := ∑ a, M a * z a with hZ
    have hp0 : 0 ≤ p := Finset.sum_nonneg fun a _ => mul_nonneg (hM a) (hb0 a)
    have hp1 : p ≤ 1 := by
      calc p ≤ ∑ a, M a := Finset.sum_le_sum fun a _ => mul_le_of_le_one_right (hM a) (hb1 a)
        _ = 1 := hM1
    have hpy : p ≤ y := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hbw a) (hM a)
    have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun a _ => mul_nonneg (hM a) (hz0 a)
    -- The missing line of case 2: `k Z / s ≥ m / 2`.
    have hΨle : Ψ ≤ Z / s + y := by
      calc Ψ ≤ ∑ a, M a * (z a / s + w a ^ 2) :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hterm a) (hM a)
        _ = Z / s + y := by
            rw [hZ, hy, Finset.sum_div, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun a _ => by ring
    have hKZ : s * m / 2 ≤ k * Z := by
      have h1 : (k : ℝ) * Ψ ≤ k * (Z / s) + k * y := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left hΨle hk0
      have h2 : m / 2 ≤ k * (Z / s) := by linarith
      calc s * m / 2 = s * (m / 2) := by ring
        _ ≤ s * (k * (Z / s)) := mul_le_mul_of_nonneg_left h2 hs.le
        _ = k * Z := by field_simp
    -- Pointwise bound and expectation.
    have hzT : ∀ (x : Fin k → α) (r : Fin k), z (x r) ≤ √(∑ r', u (x r') ^ 2) := by
      intro x r
      by_cases h : s < |u (x r)|
      · have hza : z (x r) = |u (x r)| := by simp [hz, h]
        rw [hza, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun r' _ => sq_nonneg (u (x r')))
          (Finset.mem_univ r))
      · have hza : z (x r) = 0 := by simp [hz, h]
        rw [hza]
        exact Real.sqrt_nonneg _
    have hpt : ∀ x : Fin k → α,
        ∑ r, ∏ r', (if r' = r then z (x r') else 1 - b (x r')) ≤ √(∑ r, u (x r) ^ 2) :=
      fun x => sum_prod_ite_le (fun r => z (x r)) (fun r => b (x r)) _ (fun r => hz0 _)
        (fun r => hb01 _) (fun r => hzb _) (hzT x) (Real.sqrt_nonneg _)
    have hE : ∀ r : Fin k, ∑ x : Fin k → α, (∏ i, M (x i)) *
        ∏ r', (if r' = r then z (x r') else 1 - b (x r')) =
          ∏ r', (if r' = r then Z else 1 - p) := by
      intro r
      rw [sum_prod_mul_prod_apply M (fun r' a => if r' = r then z a else 1 - b a)]
      refine Finset.prod_congr rfl fun r' _ => ?_
      by_cases h : r' = r
      · simp only [h, ↓reduceIte]
        rw [hZ]
      · simp only [h, ↓reduceIte, mul_sub, mul_one, Finset.sum_sub_distrib, hM1]
        rw [hp]
    have hprod : ∀ r : Fin k, Z * (1 - p) ^ k ≤ ∏ r', (if r' = r then Z else 1 - p) := by
      intro r
      calc Z * (1 - p) ^ k = (∏ r', (if r' = r then Z else 1)) * ∏ _r' : Fin k, (1 - p) := by
            rw [Finset.prod_ite_eq', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            simp
        _ = ∏ r', ((if r' = r then Z else 1) * (1 - p)) := Finset.prod_mul_distrib.symm
        _ ≤ ∏ r', (if r' = r then Z else 1 - p) := by
            refine Finset.prod_le_prod₀ (fun r' _ => ?_) (fun r' _ => ?_)
            · split_ifs
              · exact mul_nonneg hZ0 (by linarith)
              · linarith
            · split_ifs
              · nlinarith
              · linarith
    have hlow : (k : ℝ) * (Z * (1 - p) ^ k) ≤ A := by
      calc (k : ℝ) * (Z * (1 - p) ^ k) = ∑ _r : Fin k, Z * (1 - p) ^ k := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ ∑ r : Fin k, ∏ r', (if r' = r then Z else 1 - p) :=
            Finset.sum_le_sum fun r _ => hprod r
        _ = ∑ r : Fin k, ∑ x : Fin k → α, (∏ i, M (x i)) *
              ∏ r', (if r' = r then z (x r') else 1 - b (x r')) :=
            Finset.sum_congr rfl fun r _ => (hE r).symm
        _ = ∑ x : Fin k → α, (∏ i, M (x i)) *
              ∑ r : Fin k, ∏ r', (if r' = r then z (x r') else 1 - b (x r')) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
        _ ≤ A := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hW x)
    -- Bernoulli's inequality `(1 - p)^k ≥ 1 - k p`, and `k p ≤ k y < 1/2`.
    have hB : 1 + (k : ℝ) * -p ≤ (1 + -p) ^ k := one_add_mul_le_pow (by linarith) k
    rw [← sub_eq_add_neg] at hB
    have hkp : (k : ℝ) * p ≤ k * y := mul_le_mul_of_nonneg_left hpy hk0
    have hkZ0 : 0 ≤ (k : ℝ) * Z := mul_nonneg hk0 hZ0
    have h7 : (k : ℝ) * Z * (1 - k * p) ≤ k * (Z * (1 - p) ^ k) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hkZ0
    have h8 : (k : ℝ) * Z / 2 ≤ k * Z * (1 - k * p) := by
      nlinarith [mul_nonneg hkZ0 (by linarith : (0 : ℝ) ≤ 1 / 2 - k * p)]
    have hsm : 0 ≤ s * m := mul_nonneg hs.le hm0
    linarith

/-! ### The comparison for the AKVZ score -/

/-- The proxy as an expectation under the midpoint law:
`Ψ(s) = ∑ a, M(a) min (u(a)² / s², |u(a)| / s)`. -/
theorem akvzProxy_eq {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : ProbabilityMeasure α) (s : ℝ) :
    akvzProxy P Q s =
      ∑ a, akvzMid P Q a * min (akvzScore P Q a ^ 2 / s ^ 2) (|akvzScore P Q a| / s) :=
  rfl

/-- **Upper comparison of the score norm with the proxy** (by an elementary comparison): for `s > 0`,
`A ≤ s (√(k Ψ(s)) + k Ψ(s))`, with `A = akvzScoreNorm P Q k` and `Ψ = akvzProxy P Q`. -/
theorem akvzScoreNorm_le {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    akvzScoreNorm P Q k ≤ s * (√(k * akvzProxy P Q s) + k * akvzProxy P Q s) := by
  rw [akvzProxy_eq]
  exact sum_prod_mul_sqrt_le_proxy (akvzMid P Q) (akvzScore P Q) (akvzMid_nonneg P Q)
    (sum_akvzMid P Q) k hs

/-- **Lower comparison of the score norm with the proxy, explicit constant** (by an elementary comparison): for `s > 0`,
`s min(1, k Ψ(s)) / 5 ≤ A`, with `A = akvzScoreNorm P Q k` and `Ψ = akvzProxy P Q`. -/
theorem le_akvzScoreNorm {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    1 / 5 * s * min 1 (k * akvzProxy P Q s) ≤ akvzScoreNorm P Q k := by
  rw [akvzProxy_eq]
  exact le_sum_prod_mul_sqrt_proxy (akvzMid P Q) (akvzScore P Q) (akvzMid_nonneg P Q)
    (sum_akvzMid P Q) k hs

/-- **Lower comparison of the score norm with the proxy**: there is a
universal `c > 0` with `c s min(1, k Ψ(s)) ≤ A` for all laws `P`, `Q` on a finite set, all `k`
and all `s > 0`. One can take `c = 1/5` (`le_akvzScoreNorm`). -/
theorem exists_le_akvzScoreNorm : ∃ c : ℝ, 0 < c ∧ ∀ {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) (s : ℝ), 0 < s →
    c * s * min 1 (k * akvzProxy P Q s) ≤ akvzScoreNorm P Q k :=
  ⟨1 / 5, by norm_num, fun P Q k _ hs => le_akvzScoreNorm P Q k hs⟩

/-! ### Proof of `AKVZ26.ProductTV` -/

/-- **`AKVZ26.ProductTV` is proved** ([AKVZ26, Section 3.3] for identical factors on a finite set, through
[AKVZ26, Theorem 1.1] and the elementary comparison with the proxy that replaces Latała's
theorem). For `0 < c₁ ≤ C₁` the constants are
`c = min(1, c₁) / 1005` and `C = 201 max(1, √C₁ + C₁)`. -/
theorem akvz26_productTV : AKVZ26.ProductTV := by
  unfold AKVZ26.ProductTV
  intro c₁ C₁ hc₁ _
  have hlam0 : 0 < min 1 c₁ := lt_min one_pos hc₁
  refine ⟨min 1 c₁ / 1005, 201 * max 1 (√C₁ + C₁), div_pos hlam0 (by norm_num),
    mul_pos (by norm_num) (lt_max_of_lt_left one_pos), ?_⟩
  intro α _ _ _ P Q _ k _ s hs hK1 hK2
  obtain ⟨hTVl, hTVu⟩ := tvDist_pi_comparable_scoreNorm P Q k
  have hlow := le_akvzScoreNorm P Q k hs
  have hup := akvzScoreNorm_le P Q k hs
  have hA0 := akvzScoreNorm_nonneg P Q k
  have hlam1 : min 1 c₁ ≤ 1 := min_le_left _ _
  have hmK : min 1 c₁ ≤ min 1 ((k : ℝ) * akvzProxy P Q s) := min_le_min_left 1 hK1
  have hs0 : 0 ≤ min 1 s := le_min zero_le_one hs.le
  have hs1 : min 1 s ≤ 1 := min_le_left _ _
  constructor
  · have hAlow : min 1 c₁ / 5 * s ≤ akvzScoreNorm P Q k := by
      calc min 1 c₁ / 5 * s = 1 / 5 * s * min 1 c₁ := by ring
        _ ≤ 1 / 5 * s * min 1 ((k : ℝ) * akvzProxy P Q s) :=
            mul_le_mul_of_nonneg_left hmK (by linarith)
        _ ≤ akvzScoreNorm P Q k := hlow
    have hmin : min 1 c₁ / 5 * min 1 s ≤ min 1 (akvzScoreNorm P Q k) := by
      refine le_min ?_ ?_
      · calc min 1 c₁ / 5 * min 1 s ≤ 1 / 5 * 1 :=
              mul_le_mul (by linarith) hs1 hs0 (by norm_num)
          _ ≤ 1 := by norm_num
      · calc min 1 c₁ / 5 * min 1 s ≤ min 1 c₁ / 5 * s :=
              mul_le_mul_of_nonneg_left (min_le_right 1 s) (by linarith)
          _ ≤ akvzScoreNorm P Q k := hAlow
    calc min 1 c₁ / 1005 * min 1 s = 1 / 201 * (min 1 c₁ / 5 * min 1 s) := by ring
      _ ≤ 1 / 201 * min 1 (akvzScoreNorm P Q k) :=
          mul_le_mul_of_nonneg_left hmin (by norm_num)
      _ ≤ _ := hTVl
  · have hAup : akvzScoreNorm P Q k ≤ max 1 (√C₁ + C₁) * s := by
      calc akvzScoreNorm P Q k
          ≤ s * (√((k : ℝ) * akvzProxy P Q s) + k * akvzProxy P Q s) := hup
        _ ≤ s * (√C₁ + C₁) :=
            mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt hK2) hK2) hs.le
        _ ≤ s * max 1 (√C₁ + C₁) := mul_le_mul_of_nonneg_left (le_max_right _ _) hs.le
        _ = max 1 (√C₁ + C₁) * s := mul_comm _ _
    have hmin : min 1 (akvzScoreNorm P Q k) ≤ max 1 (√C₁ + C₁) * min 1 s := by
      rcases le_total s 1 with h | h
      · rw [min_eq_right h]
        exact (min_le_right _ _).trans hAup
      · rw [min_eq_left h, mul_one]
        exact (min_le_left _ _).trans (le_max_left _ _)
    calc _ ≤ 201 * min 1 (akvzScoreNorm P Q k) := hTVu
      _ ≤ 201 * (max 1 (√C₁ + C₁) * min 1 s) := mul_le_mul_of_nonneg_left hmin (by norm_num)
      _ = 201 * max 1 (√C₁ + C₁) * min 1 s := by ring

end Parking

end
