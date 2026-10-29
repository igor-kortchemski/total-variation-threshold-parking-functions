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

public import Parking.External
import Parking.Symmetrization
import Parking.TVDist
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Product laws through the AKVZ score

This module formalizes the representation, remainder and Hellinger estimates in
the proof of [AKVZ26, Theorem 1.1] for two laws `P`, `Q` on a finite set and identical factors.

Notation: `M = (P + Q) / 2` is the midpoint law (`akvzMid`), `u` the AKVZ score
(`akvzScore`), `a = 𝔼_M u²` (`akvzVar`) and `ρ = k a`. For `x : Fin k → α`, of law `M^{⊗k}`
with weight `W x = ∏ r, M (x r)`, put `U_r = u (x r)`, `S = ∑ r, U_r`,
`Φ = (∏ r, (1 + U_r) - ∏ r, (1 - U_r)) / 2` and `R = Φ - S`. The quantity
`A = 𝔼 (∑ r, U_r²)^{1/2}` of [AKVZ26, Theorem 1.1] is `akvzScoreNorm`.

* Basic facts: `P = M (1 + u)` and `Q = M (1 - u)` atomwise, also where `M = 0`
  (`akvzMid_mul_one_add_akvzScore`, `akvzMid_mul_one_sub_akvzScore`); `∑ M = 1`
  (`sum_akvzMid`), `∑ M u = 0` (`sum_akvzMid_mul_akvzScore`), `|u| ≤ 1`
  (`abs_akvzScore_le_one`) and `0 ≤ a ≤ 1`.
* Step 1, representation (`tvDist_pi_eq_sum_oddPart`): `d_TV(P^{⊗k}, Q^{⊗k}) = 𝔼 |Φ|`.
* Step 2, remainder (`sum_remainder_sq`): `𝔼 R² = ((1 + a)^k - (1 - a)^k) / 2 - k a`. The proof
  uses no expansion into monomials, only the three factorizations
  `𝔼 ∏ r, (1 ± U_r)² = (1 + a)^k` and `𝔼 ∏ r, (1 - U_r²) = (1 - a)^k`, together with
  `𝔼 Φ S = 𝔼 S² = k a` (`sum_prod_mul_remainder_sq`). Consequences: `𝔼 R² ≤ ρ³ / 5` for
  `ρ ≤ 1` (`sum_remainder_sq_le`, from the binomial series bound `oddPart_sub_le`), and
  `𝔼 |R| ≤ √(𝔼 R²)` (`sum_abs_remainder_le_sqrt`, `sum_abs_remainder_le`).
* Step 3, Hellinger-type lower bounds: `d_TV(P^{⊗k}, Q^{⊗k}) ≥ 1 - e^{-ρ/2}`
  (`one_sub_exp_le_tvDist_pi`), from `min (p, q) ≤ √(p q)`, and `A ≥ 1 - e^{-ρ/2}`
  (`one_sub_exp_le_akvzScoreNorm`), from `√z ≥ 1 - e^{-z}`.

The factorization lemmas are stated for an arbitrary weight `M : α → ℝ` and an arbitrary
function `u : α → ℝ`, then specialized to `M = akvzMid P Q` and `u = akvzScore P Q`.
-/

public section

open MeasureTheory

namespace Parking

/-! ### Definitions -/

/-- The midpoint law `M(a) = (P(a) + Q(a)) / 2` of two laws, as a real weight on the atoms
([AKVZ26, §1]). -/
@[expose] noncomputable def akvzMid {α : Type} [MeasurableSpace α] (P Q : ProbabilityMeasure α)
    (a : α) : ℝ :=
  ((P {a} : ℝ) + Q {a}) / 2

/-- The variance `a = 𝔼_M u² = ∑ₐ M(a) u(a)²` of the AKVZ score `u` under the midpoint law `M`. -/
@[expose] noncomputable def akvzVar {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) : ℝ :=
  ∑ a, akvzMid P Q a * akvzScore P Q a ^ 2

/-- The score norm `A = 𝔼 (∑_r u(X_r)²)^{1/2}`, for `X_1, …, X_k` independent of law `M`, the
quantity that governs `d_TV(P^{⊗k}, Q^{⊗k})` in [AKVZ26, Theorem 1.1]. -/
@[expose] noncomputable def akvzScoreNorm {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) : ℝ :=
  ∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) * √(∑ r, akvzScore P Q (x r) ^ 2)

/-! ### Factorization of expectations under a product weight -/

/-- **Factorization** under a product weight: for functions `g r` of the coordinates,
`∑ x, (∏ r, M (x r)) ∏ r, g r (x r) = ∏ r, ∑ a, M a g r a`. -/
theorem sum_prod_mul_prod_apply {α : Type*} [Fintype α] (M : α → ℝ) {k : ℕ}
    (g : Fin k → α → ℝ) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * ∏ r, g r (x r) = ∏ r, ∑ a, M a * g r a := by
  have h := Fintype.prod_sum fun (r : Fin k) (a : α) => M a * g r a
  rw [h]
  exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib.symm

/-- Factorization for a function of one coordinate:
`∑ x, (∏ r, M (x r)) ∏ r, f (x r) = (∑ a, M a f a)^k`. -/
theorem sum_prod_mul_prod {α : Type*} [Fintype α] (M f : α → ℝ) (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * ∏ r, f (x r) = (∑ a, M a * f a) ^ k := by
  rw [sum_prod_mul_prod_apply M fun _ => f, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Factorization with one marked coordinate `s`: if `∑ a, M a f a = 1`, then
`∑ x, (∏ r, M (x r)) ((∏ r, f (x r)) g (x s)) = ∑ a, M a (f a g a)`. -/
theorem sum_prod_mul_prod_mul_apply {α : Type*} [Fintype α] (M f g : α → ℝ)
    (hf : ∑ a, M a * f a = 1) {k : ℕ} (s : Fin k) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * ((∏ r, f (x r)) * g (x s)) = ∑ a, M a * (f a * g a) := by
  have h := sum_prod_mul_prod_apply M fun r a => f a * if r = s then g a else 1
  have e1 : ∀ x : Fin k → α,
      ∏ r, (f (x r) * if r = s then g (x r) else 1) = (∏ r, f (x r)) * g (x s) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  have e2 : ∀ r : Fin k, ∑ a, M a * (f a * if r = s then g a else 1) =
      if r = s then ∑ a, M a * (f a * g a) else 1 := by
    intro r
    split_ifs
    · rfl
    · simpa only [mul_one] using hf
  simp only [e1, e2, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  exact h

/-- Second moments of a centred function under a product weight: if `∑ a, M a = 1` and
`∑ a, M a u a = 0`, then `∑ x, (∏ i, M (x i)) u (x r) u (x s)` is `∑ a, M a u a²` for `r = s`
and `0` otherwise. -/
theorem sum_prod_mul_apply_mul_apply {α : Type*} [Fintype α] (M u : α → ℝ)
    (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) {k : ℕ} (r s : Fin k) :
    ∑ x : Fin k → α, (∏ i, M (x i)) * (u (x r) * u (x s)) =
      if r = s then ∑ a, M a * u a ^ 2 else 0 := by
  split_ifs with hrs
  · subst hrs
    have h := sum_prod_mul_prod_mul_apply M (fun _ => 1) (fun a => u a ^ 2)
      (by simpa only [mul_one] using hM1) r
    simp only [Finset.prod_const_one, one_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => by ring
  · have h := sum_prod_mul_prod_apply M fun i a =>
      (if i = r then u a else 1) * (if i = s then u a else 1)
    have e1 : ∀ x : Fin k → α, ∏ i, ((if i = r then u (x i) else 1) *
        (if i = s then u (x i) else 1)) = u (x r) * u (x s) := by
      intro x
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
      simp
    have e2 : ∏ i, ∑ a, M a * ((if i = r then u a else 1) * (if i = s then u a else 1)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hrs, hu])
    simp only [e1] at h
    rw [h, e2]

/-- `𝔼 S² = k a` for the sum `S = ∑ r, u (x r)` of `k` independent centred coordinates:
`∑ x, (∏ r, M (x r)) (∑ r, u (x r))² = k ∑ a, M a u a²`. -/
theorem sum_prod_mul_sum_sq {α : Type*} [Fintype α] (M u : α → ℝ) (hM1 : ∑ a, M a = 1)
    (hu : ∑ a, M a * u a = 0) (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * (∑ r, u (x r)) ^ 2 = k * ∑ a, M a * u a ^ 2 := by
  calc ∑ x : Fin k → α, (∏ r, M (x r)) * (∑ r, u (x r)) ^ 2
      = ∑ x : Fin k → α, ∑ r, ∑ s, (∏ i, M (x i)) * (u (x r) * u (x s)) :=
        Finset.sum_congr rfl fun x _ => by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ => Finset.mul_sum _ _ _
    _ = ∑ r, ∑ s, ∑ x : Fin k → α, (∏ i, M (x i)) * (u (x r) * u (x s)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ r : Fin k, ∑ s : Fin k, if r = s then ∑ a, M a * u a ^ 2 else 0 := by
        simp only [sum_prod_mul_apply_mul_apply M u hM1 hu]
    _ = k * ∑ a, M a * u a ^ 2 := by simp

/-- `𝔼 (∏ r, f (x r)) S = k ∑ a, M a f a u a` for `S = ∑ r, u (x r)`, when
`∑ a, M a f a = 1`. -/
theorem sum_prod_mul_prod_mul_sum {α : Type*} [Fintype α] (M f u : α → ℝ)
    (hf : ∑ a, M a * f a = 1) (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * ((∏ r, f (x r)) * ∑ r, u (x r)) =
      k * ∑ a, M a * (f a * u a) := by
  calc ∑ x : Fin k → α, (∏ r, M (x r)) * ((∏ r, f (x r)) * ∑ r, u (x r))
      = ∑ x : Fin k → α, ∑ s, (∏ r, M (x r)) * ((∏ r, f (x r)) * u (x s)) :=
        Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ s, ∑ x : Fin k → α, (∏ r, M (x r)) * ((∏ r, f (x r)) * u (x s)) := Finset.sum_comm
    _ = ∑ s : Fin k, ∑ a, M a * (f a * u a) := by
        simp only [sum_prod_mul_prod_mul_apply M f u hf]
    _ = k * ∑ a, M a * (f a * u a) := by simp

/-- **Second moment of the remainder** under a product weight. If
`∑ a, M a = 1` and `∑ a, M a u a = 0`, and `v = ∑ a, M a u a²`, then
`𝔼 (Φ - S)² = ((1 + v)^k - (1 - v)^k) / 2 - k v`, where
`Φ = (∏ r, (1 + U_r) - ∏ r, (1 - U_r)) / 2` and `S = ∑ r, U_r`. The proof uses the three
factorizations `𝔼 ∏ r, (1 ± U_r)² = (1 + v)^k` and `𝔼 ∏ r, (1 - U_r²) = (1 - v)^k`, and
`𝔼 (∏ r, (1 ± U_r)) S = ± k v`, `𝔼 S² = k v`. -/
theorem sum_prod_mul_remainder_sq {α : Type*} [Fintype α] (M u : α → ℝ)
    (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, M (x r)) *
        ((∏ r, (1 + u (x r)) - ∏ r, (1 - u (x r))) / 2 - ∑ r, u (x r)) ^ 2 =
      ((1 + ∑ a, M a * u a ^ 2) ^ k - (1 - ∑ a, M a * u a ^ 2) ^ k) / 2 -
        k * ∑ a, M a * u a ^ 2 := by
  obtain ⟨v, hv⟩ : ∃ v, ∑ a, M a * u a ^ 2 = v := ⟨_, rfl⟩
  rw [hv]
  -- Expectations of quadratic polynomials in `u`.
  have hsum : ∀ (f : α → ℝ) (c₀ c₁ c₂ : ℝ), (∀ a, f a = c₀ + c₁ * u a + c₂ * u a ^ 2) →
      ∑ a, M a * f a = c₀ + c₂ * v := by
    intro f c₀ c₁ c₂ hf
    have e : ∀ a, M a * f a = c₀ * M a + c₁ * (M a * u a) + c₂ * (M a * u a ^ 2) := fun a => by
      rw [hf a]; ring
    rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hM1, hu, hv]
    ring
  have hA : ∑ a, M a * (1 + u a) = 1 := by
    rw [hsum (fun a => 1 + u a) 1 1 0 fun a => by ring]; ring
  have hB : ∑ a, M a * (1 - u a) = 1 := by
    rw [hsum (fun a => 1 - u a) 1 (-1) 0 fun a => by ring]; ring
  have hAA : ∑ x : Fin k → α, (∏ r, M (x r)) * ∏ r, (1 + u (x r)) ^ 2 = (1 + v) ^ k := by
    rw [sum_prod_mul_prod M (fun a => (1 + u a) ^ 2) k,
      hsum (fun a => (1 + u a) ^ 2) 1 2 1 fun a => by ring]
    ring
  have hBB : ∑ x : Fin k → α, (∏ r, M (x r)) * ∏ r, (1 - u (x r)) ^ 2 = (1 + v) ^ k := by
    rw [sum_prod_mul_prod M (fun a => (1 - u a) ^ 2) k,
      hsum (fun a => (1 - u a) ^ 2) 1 (-2) 1 fun a => by ring]
    ring
  have hAB : ∑ x : Fin k → α, (∏ r, M (x r)) * ∏ r, ((1 + u (x r)) * (1 - u (x r))) =
      (1 - v) ^ k := by
    rw [sum_prod_mul_prod M (fun a => (1 + u a) * (1 - u a)) k,
      hsum (fun a => (1 + u a) * (1 - u a)) 1 0 (-1) fun a => by ring]
    ring
  have hAS : ∑ x : Fin k → α, (∏ r, M (x r)) * ((∏ r, (1 + u (x r))) * ∑ r, u (x r)) =
      k * v := by
    rw [sum_prod_mul_prod_mul_sum M (fun a => 1 + u a) u hA k,
      hsum (fun a => (1 + u a) * u a) 0 1 1 fun a => by ring]
    ring
  have hBS : ∑ x : Fin k → α, (∏ r, M (x r)) * ((∏ r, (1 - u (x r))) * ∑ r, u (x r)) =
      -(k * v) := by
    rw [sum_prod_mul_prod_mul_sum M (fun a => 1 - u a) u hB k,
      hsum (fun a => (1 - u a) * u a) 0 1 (-1) fun a => by ring]
    ring
  have hSS : ∑ x : Fin k → α, (∏ r, M (x r)) * (∑ r, u (x r)) ^ 2 = k * v := by
    rw [sum_prod_mul_sum_sq M u hM1 hu k, hv]
  have key : ∀ x : Fin k → α, (∏ r, M (x r)) *
      ((∏ r, (1 + u (x r)) - ∏ r, (1 - u (x r))) / 2 - ∑ r, u (x r)) ^ 2 =
      1 / 4 * ((∏ r, M (x r)) * ∏ r, (1 + u (x r)) ^ 2) +
        1 / 4 * ((∏ r, M (x r)) * ∏ r, (1 - u (x r)) ^ 2) -
        1 / 2 * ((∏ r, M (x r)) * ∏ r, ((1 + u (x r)) * (1 - u (x r)))) -
        ((∏ r, M (x r)) * ((∏ r, (1 + u (x r))) * ∑ r, u (x r)) -
          (∏ r, M (x r)) * ((∏ r, (1 - u (x r))) * ∑ r, u (x r))) +
        (∏ r, M (x r)) * (∑ r, u (x r)) ^ 2 := by
    intro x
    rw [Finset.prod_pow, Finset.prod_pow, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl fun x _ => key x]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hAA, hBB, hAB, hAS, hBS, hSS]
  ring

/-! ### Elementary inequalities -/

/-- `e^{-t} ≤ 1 - t / 2` for `0 ≤ t ≤ 1`. -/
theorem exp_neg_le_one_sub_half {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.exp (-t) ≤ 1 - t / 2 := by
  have hpos : 0 < 1 + t := by linarith
  have he : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  calc Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
    _ ≤ (1 + t)⁻¹ := inv_anti₀ hpos he
    _ = 1 / (1 + t) := (one_div _).symm
    _ ≤ 1 - t / 2 := by
        rw [div_le_iff₀ hpos]
        nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]

/-- `1 - e^{-z} ≤ √z` for `z ≥ 0`. -/
theorem one_sub_exp_neg_le_sqrt {z : ℝ} (hz : 0 ≤ z) : 1 - Real.exp (-z) ≤ √z := by
  rcases le_total z 1 with h | h
  · have h1 : z ≤ √z := (Real.le_sqrt hz hz).2 (by nlinarith)
    linarith [Real.one_sub_le_exp_neg z]
  · have h1 : 1 ≤ √z := by simpa using Real.sqrt_le_sqrt h
    linarith [Real.exp_pos (-z)]

/-- `(1 - a / 2)^k ≤ e^{-k a / 2}` for `a ≤ 2`. -/
theorem one_sub_half_pow_le_exp {a : ℝ} (ha : a ≤ 2) (k : ℕ) :
    (1 - a / 2) ^ k ≤ Real.exp (-(k * a) / 2) := by
  have h0 : 0 ≤ 1 - a / 2 := by linarith
  have h1 : 1 - a / 2 ≤ Real.exp (-a / 2) := by linarith [Real.add_one_le_exp (-a / 2)]
  calc (1 - a / 2) ^ k ≤ Real.exp (-a / 2) ^ k := pow_le_pow_left₀ h0 h1 k
    _ = Real.exp (-(k * a) / 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- `120 · 2^j ≤ (j + 5)!`. -/
theorem mul_two_pow_le_factorial_add_five (j : ℕ) : 120 * 2 ^ j ≤ (j + 5).factorial := by
  induction j with
  | zero => norm_num [Nat.factorial]
  | succ j ih =>
    calc 120 * 2 ^ (j + 1) = 2 * (120 * 2 ^ j) := by ring
      _ ≤ (j + 6) * (j + 5).factorial := Nat.mul_le_mul (by omega) ih
      _ = (j + 1 + 5).factorial := (Nat.factorial_succ (j + 5)).symm

/-- **Series bound for the remainder**: for `a ≥ 0` and `ρ = k a ≤ 1`,
`((1 + a)^k - (1 - a)^k) / 2 - k a ≤ ρ³ / 5`. The left side is `∑_{j ≥ 3 odd} C(k, j) a^j`, and
`C(k, j) a^j ≤ ρ^j / j! ≤ ρ³ / j!` for `j ≥ 3` (`Nat.choose_le_pow_div`); the term `j = 3` gives
`ρ³ / 6` and the terms `j ≥ 5` at most `ρ³ / 60`. -/
theorem oddPart_sub_le {a : ℝ} (ha : 0 ≤ a) {k : ℕ} (hka : (k : ℝ) * a ≤ 1) :
    ((1 + a) ^ k - (1 - a) ^ k) / 2 - k * a ≤ ((k : ℝ) * a) ^ 3 / 5 := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, (k : ℝ) * a = ρ := ⟨_, rfl⟩
  rw [hρ] at hka ⊢
  have hρ0 : 0 ≤ ρ := hρ ▸ mul_nonneg (Nat.cast_nonneg k) ha
  -- The binomial expansion of the odd part.
  have e : ((1 + a) ^ k - (1 - a) ^ k) / 2 =
      ∑ j ∈ Finset.range (k + 1), (a ^ j - (-a) ^ j) / 2 * (k.choose j : ℝ) := by
    rw [add_comm (1 : ℝ) a, show (1 : ℝ) - a = -a + 1 by ring, add_pow, add_pow,
      ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [one_pow, mul_one]
    ring
  -- Termwise bounds.
  have hchoose : ∀ j, (k.choose j : ℝ) * a ^ j ≤ ρ ^ j / j.factorial := by
    intro j
    calc (k.choose j : ℝ) * a ^ j ≤ (k : ℝ) ^ j / j.factorial * a ^ j :=
          mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div j k) (pow_nonneg ha j)
      _ = ρ ^ j / j.factorial := by rw [← hρ, mul_pow]; ring
  have hodd : ∀ j, (a ^ j - (-a) ^ j) / 2 * (k.choose j : ℝ) ≤ (k.choose j : ℝ) * a ^ j := by
    intro j
    have h1 : -(-a) ^ j ≤ a ^ j :=
      (neg_le_abs _).trans_eq (by rw [abs_pow, abs_neg, abs_of_nonneg ha])
    calc (a ^ j - (-a) ^ j) / 2 * (k.choose j : ℝ) ≤ a ^ j * (k.choose j : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      _ = (k.choose j : ℝ) * a ^ j := mul_comm _ _
  let g : ℕ → ℝ := fun j => match j with
    | 0 => 0
    | 1 => ρ
    | 2 => 0
    | 3 => ρ ^ 3 / 6
    | 4 => 0
    | j + 5 => ρ ^ 3 / 120 * (1 / 2) ^ j
  have hg0 : ∀ j, 0 ≤ g j := by
    intro j
    match j with
    | 0 => exact le_rfl
    | 1 => exact hρ0
    | 2 => exact le_rfl
    | 3 => exact div_nonneg (pow_nonneg hρ0 3) (by norm_num)
    | 4 => exact le_rfl
    | j + 5 => exact mul_nonneg (div_nonneg (pow_nonneg hρ0 3) (by norm_num)) (by positivity)
  have htg : ∀ j, (a ^ j - (-a) ^ j) / 2 * (k.choose j : ℝ) ≤ g j := by
    intro j
    match j with
    | 0 =>
      show (a ^ 0 - (-a) ^ 0) / 2 * (k.choose 0 : ℝ) ≤ 0
      simp
    | 1 =>
      show (a ^ 1 - (-a) ^ 1) / 2 * (k.choose 1 : ℝ) ≤ ρ
      exact le_of_eq (by rw [Nat.choose_one_right, ← hρ]; ring)
    | 2 =>
      show (a ^ 2 - (-a) ^ 2) / 2 * (k.choose 2 : ℝ) ≤ 0
      rw [neg_sq, sub_self, zero_div, zero_mul]
    | 3 =>
      show (a ^ 3 - (-a) ^ 3) / 2 * (k.choose 3 : ℝ) ≤ ρ ^ 3 / 6
      calc (a ^ 3 - (-a) ^ 3) / 2 * (k.choose 3 : ℝ) ≤ (k.choose 3 : ℝ) * a ^ 3 := hodd 3
        _ ≤ ρ ^ 3 / (Nat.factorial 3 : ℝ) := hchoose 3
        _ = ρ ^ 3 / 6 := by norm_num [Nat.factorial]
    | 4 =>
      show (a ^ 4 - (-a) ^ 4) / 2 * (k.choose 4 : ℝ) ≤ 0
      rw [show (-a) ^ 4 = a ^ 4 by ring, sub_self, zero_div, zero_mul]
    | j + 5 =>
      show (a ^ (j + 5) - (-a) ^ (j + 5)) / 2 * (k.choose (j + 5) : ℝ) ≤
        ρ ^ 3 / 120 * (1 / 2) ^ j
      have hfac : (120 : ℝ) * 2 ^ j ≤ ((j + 5).factorial : ℝ) := by
        exact_mod_cast mul_two_pow_le_factorial_add_five j
      calc (a ^ (j + 5) - (-a) ^ (j + 5)) / 2 * (k.choose (j + 5) : ℝ)
          ≤ (k.choose (j + 5) : ℝ) * a ^ (j + 5) := hodd (j + 5)
        _ ≤ ρ ^ (j + 5) / ((j + 5).factorial : ℝ) := hchoose (j + 5)
        _ ≤ ρ ^ 3 / ((j + 5).factorial : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_of_le_one hρ0 hka (by omega))
            (Nat.cast_nonneg _)
        _ ≤ ρ ^ 3 / (120 * 2 ^ j) :=
          div_le_div_of_nonneg_left (pow_nonneg hρ0 3) (by positivity) hfac
        _ = ρ ^ 3 / 120 * (1 / 2) ^ j := by
          rw [one_div_pow, div_mul_div_comm, mul_one]
  have hsum : ∑ j ∈ Finset.range (k + 1), g j ≤ ρ + ρ ^ 3 / 5 := by
    calc ∑ j ∈ Finset.range (k + 1), g j ≤ ∑ j ∈ Finset.range (5 + (k + 1)), g j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            fun j _ _ => hg0 j
      _ = ∑ j ∈ Finset.range 5, g j + ∑ j ∈ Finset.range (k + 1), g (5 + j) :=
          Finset.sum_range_add _ _ _
      _ = ρ + ρ ^ 3 / 6 + ρ ^ 3 / 120 * ∑ j ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ j := by
          rw [Finset.mul_sum]
          congr 1
          · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
            show (0 : ℝ) + 0 + ρ + 0 + ρ ^ 3 / 6 + 0 = ρ + ρ ^ 3 / 6
            ring
          · exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm 5 j]
      _ ≤ ρ + ρ ^ 3 / 6 + ρ ^ 3 / 120 * 2 := by
          have := mul_le_mul_of_nonneg_left (sum_geometric_two_le (k + 1))
            (div_nonneg (pow_nonneg hρ0 3) (by norm_num : (0 : ℝ) ≤ 120))
          linarith
      _ ≤ ρ + ρ ^ 3 / 5 := by linarith [pow_nonneg hρ0 3]
  rw [e]
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.range (k + 1)) => htg j
  linarith

/-- **Weighted Cauchy–Schwarz**: for probability weights `w`, `∑ w |f| ≤ √(∑ w f²)`. -/
theorem sum_mul_abs_le_sqrt_sum_mul_sq {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) :
    ∑ i ∈ s, w i * |f i| ≤ √(∑ i ∈ s, w i * f i ^ 2) := by
  have h := Real.sum_sqrt_mul_sqrt_le (f := w) (g := fun i => w i * f i ^ 2) s hw
    fun i => mul_nonneg (hw i) (sq_nonneg (f i))
  rw [hw1, Real.sqrt_one, one_mul] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.sqrt_mul (hw i), Real.sqrt_sq_eq_abs, ← mul_assoc, Real.mul_self_sqrt (hw i)]

/-- `∑ a, M a u a² ≤ 1` for a probability weight `M` and `|u| ≤ 1`. -/
theorem sum_mul_sq_le_one {α : Type*} [Fintype α] (M u : α → ℝ) (hM : ∀ a, 0 ≤ M a)
    (hM1 : ∑ a, M a = 1) (hu1 : ∀ a, |u a| ≤ 1) : ∑ a, M a * u a ^ 2 ≤ 1 := by
  calc ∑ a, M a * u a ^ 2 ≤ ∑ a, M a := Finset.sum_le_sum fun a _ =>
        mul_le_of_le_one_right (hM a) ((sq_le_one_iff_abs_le_one _).2 (hu1 a))
    _ = 1 := hM1

/-- `∑ a, M a (1 - u a² / 2) = 1 - (∑ a, M a u a²) / 2` for a weight of total mass one. -/
theorem sum_mul_one_sub_sq_div_two {α : Type*} [Fintype α] (M u : α → ℝ)
    (hM1 : ∑ a, M a = 1) : ∑ a, M a * (1 - u a ^ 2 / 2) = 1 - (∑ a, M a * u a ^ 2) / 2 := by
  have e : ∀ a, M a * (1 - u a ^ 2 / 2) = M a - M a * u a ^ 2 / 2 := fun a => by ring
  rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_sub_distrib, ← Finset.sum_div, hM1]

/-! ### Hellinger-type lower bounds -/

/-- Pointwise Hellinger-type bound: if `|v r| ≤ 1` for every `r`, then
`min (∏ r, (1 + v r)) (∏ r, (1 - v r)) ≤ ∏ r, (1 - v r² / 2)`. It combines
`min (p, q)² ≤ p q = ∏ r, (1 - v r²)` with `1 - t ≤ (1 - t / 2)²`. -/
theorem min_prod_le_prod {k : ℕ} (v : Fin k → ℝ) (hv : ∀ r, |v r| ≤ 1) :
    min (∏ r, (1 + v r)) (∏ r, (1 - v r)) ≤ ∏ r, (1 - v r ^ 2 / 2) := by
  have hv' : ∀ r, -1 ≤ v r ∧ v r ≤ 1 := fun r => abs_le.1 (hv r)
  have hsq : ∀ r, v r ^ 2 ≤ 1 := fun r => (sq_le_one_iff_abs_le_one _).2 (hv r)
  have hA : 0 ≤ ∏ r, (1 + v r) := Finset.prod_nonneg fun r _ => by linarith [(hv' r).1]
  have hB : 0 ≤ ∏ r, (1 - v r) := Finset.prod_nonneg fun r _ => by linarith [(hv' r).2]
  have hC : 0 ≤ ∏ r, (1 - v r ^ 2 / 2) := Finset.prod_nonneg fun r _ => by linarith [hsq r]
  have hm : 0 ≤ min (∏ r, (1 + v r)) (∏ r, (1 - v r)) := le_min hA hB
  have h1 : min (∏ r, (1 + v r)) (∏ r, (1 - v r)) ^ 2 ≤ (∏ r, (1 + v r)) * ∏ r, (1 - v r) := by
    rw [sq]
    exact mul_le_mul (min_le_left _ _) (min_le_right _ _) hm hA
  have h2 : (∏ r, (1 + v r)) * ∏ r, (1 - v r) ≤ (∏ r, (1 - v r ^ 2 / 2)) ^ 2 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
    exact Finset.prod_le_prod₀ (fun r _ => by nlinarith [hsq r])
      fun r _ => by nlinarith [sq_nonneg (v r ^ 2)]
  exact (sq_le_sq₀ hm hC).1 (h1.trans h2)

/-- Hellinger-type bound under a product weight: for a probability weight `M` and `|u| ≤ 1`,
`𝔼 min (∏ r, (1 + U_r), ∏ r, (1 - U_r)) ≤ e^{-k v / 2}` with `v = ∑ a, M a u a²`. -/
theorem sum_prod_mul_min_le {α : Type*} [Fintype α] (M u : α → ℝ) (hM : ∀ a, 0 ≤ M a)
    (hM1 : ∑ a, M a = 1) (hu1 : ∀ a, |u a| ≤ 1) (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * min (∏ r, (1 + u (x r))) (∏ r, (1 - u (x r))) ≤
      Real.exp (-(k * ∑ a, M a * u a ^ 2) / 2) := by
  calc ∑ x : Fin k → α, (∏ r, M (x r)) * min (∏ r, (1 + u (x r))) (∏ r, (1 - u (x r)))
      ≤ ∑ x : Fin k → α, (∏ r, M (x r)) * ∏ r, (1 - u (x r) ^ 2 / 2) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (min_prod_le_prod (fun r => u (x r)) fun r => hu1 (x r))
          (Finset.prod_nonneg fun r _ => hM _)
    _ = (1 - (∑ a, M a * u a ^ 2) / 2) ^ k := by
        rw [sum_prod_mul_prod M (fun a => 1 - u a ^ 2 / 2) k, sum_mul_one_sub_sq_div_two M u hM1]
    _ ≤ Real.exp (-(k * ∑ a, M a * u a ^ 2) / 2) :=
        one_sub_half_pow_le_exp (by linarith [sum_mul_sq_le_one M u hM hM1 hu1]) k

/-- Lower bound on the score norm under a product weight: for a probability weight `M` and
`|u| ≤ 1`, `1 - e^{-k v / 2} ≤ 𝔼 √(∑ r, U_r²)` with `v = ∑ a, M a u a²`. It uses
`√z ≥ 1 - e^{-z}`, the factorization `𝔼 e^{-∑ r, U_r²} = (𝔼 e^{-u²})^k` and `e^{-t} ≤ 1 - t / 2`
on `[0, 1]`. -/
theorem one_sub_exp_le_sum_prod_mul_sqrt {α : Type*} [Fintype α] (M u : α → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hM1 : ∑ a, M a = 1) (hu1 : ∀ a, |u a| ≤ 1) (k : ℕ) :
    1 - Real.exp (-(k * ∑ a, M a * u a ^ 2) / 2) ≤
      ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) := by
  have hW : ∀ x : Fin k → α, 0 ≤ ∏ r, M (x r) := fun x => Finset.prod_nonneg fun r _ => hM _
  have hE : ∑ x : Fin k → α, (∏ r, M (x r)) * (1 - Real.exp (-∑ r, u (x r) ^ 2)) =
      1 - (∑ a, M a * Real.exp (-(u a ^ 2))) ^ k := by
    have e : ∀ x : Fin k → α, (∏ r, M (x r)) * (1 - Real.exp (-∑ r, u (x r) ^ 2)) =
        (∏ r, M (x r)) - (∏ r, M (x r)) * ∏ r, Real.exp (-(u (x r) ^ 2)) := by
      intro x
      rw [← Real.exp_sum, Finset.sum_neg_distrib]
      ring
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_sub_distrib, sum_prod_eq_one M hM1 k,
      sum_prod_mul_prod M (fun a => Real.exp (-(u a ^ 2))) k]
  have hle : ∑ a, M a * Real.exp (-(u a ^ 2)) ≤ 1 - (∑ a, M a * u a ^ 2) / 2 := by
    rw [← sum_mul_one_sub_sq_div_two M u hM1]
    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
      (exp_neg_le_one_sub_half (sq_nonneg _) ((sq_le_one_iff_abs_le_one _).2 (hu1 a))) (hM a)
  have h0 : 0 ≤ ∑ a, M a * Real.exp (-(u a ^ 2)) :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hM a) (Real.exp_pos _).le
  have hpow := (pow_le_pow_left₀ h0 hle k).trans
    (one_sub_half_pow_le_exp (by linarith [sum_mul_sq_le_one M u hM hM1 hu1]) k)
  calc 1 - Real.exp (-(k * ∑ a, M a * u a ^ 2) / 2)
      ≤ ∑ x : Fin k → α, (∏ r, M (x r)) * (1 - Real.exp (-∑ r, u (x r) ^ 2)) := by
        rw [hE]; linarith
    _ ≤ ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (one_sub_exp_neg_le_sqrt (Finset.sum_nonneg fun r _ => sq_nonneg _)) (hW x)

/-! ### Basic facts on the midpoint law and the score -/

/-- The midpoint weight is nonnegative. -/
theorem akvzMid_nonneg {α : Type} [MeasurableSpace α] (P Q : ProbabilityMeasure α) (a : α) :
    0 ≤ akvzMid P Q a := by
  unfold akvzMid
  positivity

/-- The product weight `∏ r, M (x r)` is nonnegative. -/
theorem prod_akvzMid_nonneg {α : Type} [MeasurableSpace α] (P Q : ProbabilityMeasure α) {k : ℕ}
    (x : Fin k → α) : 0 ≤ ∏ r, akvzMid P Q (x r) :=
  Finset.prod_nonneg fun r _ => akvzMid_nonneg P Q (x r)

/-- The midpoint weight has total mass one: `∑ₐ M(a) = 1`. -/
theorem sum_akvzMid {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : ProbabilityMeasure α) : ∑ a, akvzMid P Q a = 1 := by
  simp only [akvzMid]
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_coe_apply_singleton, sum_coe_apply_singleton]
  norm_num

/-- `P(a) = M(a) (1 + u(a))` for every atom `a`, including those with `M(a) = 0`, where both
sides vanish. -/
theorem akvzMid_mul_one_add_akvzScore {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (a : α) :
    akvzMid P Q a * (1 + akvzScore P Q a) = P {a} := by
  unfold akvzMid akvzScore
  have hp : (0 : ℝ) ≤ P {a} := NNReal.coe_nonneg _
  have hq : (0 : ℝ) ≤ Q {a} := NNReal.coe_nonneg _
  rcases (add_nonneg hp hq).eq_or_lt with h | h
  · have hp0 : (P {a} : ℝ) = 0 := by linarith
    have hq0 : (Q {a} : ℝ) = 0 := by linarith
    rw [hp0, hq0]
    simp
  · have hd : ((P {a} : ℝ) - Q {a}) / ((P {a} : ℝ) + Q {a}) * ((P {a} : ℝ) + Q {a}) =
        (P {a} : ℝ) - Q {a} := div_mul_cancel₀ _ h.ne'
    linear_combination (1 / 2 : ℝ) * hd

/-- `Q(a) = M(a) (1 - u(a))` for every atom `a`, including those with `M(a) = 0`, where both
sides vanish. -/
theorem akvzMid_mul_one_sub_akvzScore {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (a : α) :
    akvzMid P Q a * (1 - akvzScore P Q a) = Q {a} := by
  unfold akvzMid akvzScore
  have hp : (0 : ℝ) ≤ P {a} := NNReal.coe_nonneg _
  have hq : (0 : ℝ) ≤ Q {a} := NNReal.coe_nonneg _
  rcases (add_nonneg hp hq).eq_or_lt with h | h
  · have hp0 : (P {a} : ℝ) = 0 := by linarith
    have hq0 : (Q {a} : ℝ) = 0 := by linarith
    rw [hp0, hq0]
    simp
  · have hd : ((P {a} : ℝ) - Q {a}) / ((P {a} : ℝ) + Q {a}) * ((P {a} : ℝ) + Q {a}) =
        (P {a} : ℝ) - Q {a} := div_mul_cancel₀ _ h.ne'
    linear_combination (-1 / 2 : ℝ) * hd

/-- The AKVZ score takes values in `[-1, 1]`. -/
theorem abs_akvzScore_le_one {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : ProbabilityMeasure α) (a : α) : |akvzScore P Q a| ≤ 1 := by
  unfold akvzScore
  have hp : (0 : ℝ) ≤ P {a} := NNReal.coe_nonneg _
  have hq : (0 : ℝ) ≤ Q {a} := NNReal.coe_nonneg _
  rcases (add_nonneg hp hq).eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]
    exact zero_le_one
  · rw [abs_div, abs_of_pos h, div_le_one h]
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The AKVZ score is centred under the midpoint law: `∑ₐ M(a) u(a) = 0`, since
`M(a) u(a) = (P(a) - Q(a)) / 2`. -/
theorem sum_akvzMid_mul_akvzScore {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) :
    ∑ a, akvzMid P Q a * akvzScore P Q a = 0 := by
  have h : ∀ a, akvzMid P Q a * akvzScore P Q a = ((P {a} : ℝ) - Q {a}) / 2 := by
    intro a
    have h1 := akvzMid_mul_one_add_akvzScore P Q a
    have h2 := akvzMid_mul_one_sub_akvzScore P Q a
    linear_combination (h1 - h2) / 2
  rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.sum_div, Finset.sum_sub_distrib,
    sum_coe_apply_singleton, sum_coe_apply_singleton]
  norm_num

/-- `akvzVar P Q ≥ 0`. -/
theorem akvzVar_nonneg {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : ProbabilityMeasure α) : 0 ≤ akvzVar P Q :=
  Finset.sum_nonneg fun a _ => mul_nonneg (akvzMid_nonneg P Q a) (sq_nonneg _)

/-- `akvzVar P Q ≤ 1`, since `|u| ≤ 1`. -/
theorem akvzVar_le_one {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : ProbabilityMeasure α) : akvzVar P Q ≤ 1 :=
  sum_mul_sq_le_one _ _ (akvzMid_nonneg P Q) (sum_akvzMid P Q) (abs_akvzScore_le_one P Q)

/-- `akvzScoreNorm P Q k ≥ 0`. -/
theorem akvzScoreNorm_nonneg {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) :
    0 ≤ akvzScoreNorm P Q k :=
  Finset.sum_nonneg fun x _ => mul_nonneg (prod_akvzMid_nonneg P Q x) (Real.sqrt_nonneg _)

/-! ### Product laws -/

/-- The mass of an atom under the product law: `P^{⊗k}(x) = ∏ r, P(x r)`. -/
theorem coe_pi_apply_singleton {α : Type*} [MeasurableSpace α] (P : ProbabilityMeasure α)
    {k : ℕ} (x : Fin k → α) :
    ((ProbabilityMeasure.pi fun _ : Fin k => P) {x} : ℝ) = ∏ r, (P {x r} : ℝ) := by
  have h : ({x} : Set (Fin k → α)) = Set.univ.pi fun r => {x r} := by
    ext y
    simp [funext_iff]
  rw [h, ProbabilityMeasure.pi_pi, NNReal.coe_prod]

/-- `P^{⊗k}(x) = (∏ r, M(x r)) ∏ r, (1 + u(x r))`. -/
theorem coe_pi_apply_singleton_eq_mul_one_add {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) {k : ℕ} (x : Fin k → α) :
    ((ProbabilityMeasure.pi fun _ : Fin k => P) {x} : ℝ) =
      (∏ r, akvzMid P Q (x r)) * ∏ r, (1 + akvzScore P Q (x r)) := by
  rw [coe_pi_apply_singleton, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun r _ => (akvzMid_mul_one_add_akvzScore P Q (x r)).symm

/-- `Q^{⊗k}(x) = (∏ r, M(x r)) ∏ r, (1 - u(x r))`. -/
theorem coe_pi_apply_singleton_eq_mul_one_sub {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) {k : ℕ} (x : Fin k → α) :
    ((ProbabilityMeasure.pi fun _ : Fin k => Q) {x} : ℝ) =
      (∏ r, akvzMid P Q (x r)) * ∏ r, (1 - akvzScore P Q (x r)) := by
  rw [coe_pi_apply_singleton, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun r _ => (akvzMid_mul_one_sub_akvzScore P Q (x r)).symm

/-! ### Steps 1–3 of the proof of [AKVZ26, Theorem 1.1] -/

/-- **Step 1, representation** ([AKVZ26, proof of Theorem 1.1]): `d_TV(P^{⊗k}, Q^{⊗k}) = 𝔼 |Φ|`, where
`Φ = (∏ r, (1 + U_r) - ∏ r, (1 - U_r)) / 2`, `U_r = u(X_r)` and `X_1, …, X_k` are independent
of law `M = (P + Q) / 2`. -/
theorem tvDist_pi_eq_sum_oddPart {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) :
    tvDist (ProbabilityMeasure.pi fun _ : Fin k => P)
        (ProbabilityMeasure.pi fun _ : Fin k => Q) =
      ∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) *
        |(∏ r, (1 + akvzScore P Q (x r)) - ∏ r, (1 - akvzScore P Q (x r))) / 2| := by
  rw [tvDist, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coe_pi_apply_singleton_eq_mul_one_add P Q, coe_pi_apply_singleton_eq_mul_one_sub P Q,
    ← mul_sub, abs_mul, abs_of_nonneg (prod_akvzMid_nonneg P Q x), abs_div, abs_two]
  ring

/-- **Step 2, second moment of the remainder** ([AKVZ26, proof of Theorem 1.1]): with `a = akvzVar P Q`,
`𝔼 (Φ - S)² = ((1 + a)^k - (1 - a)^k) / 2 - k a`, where `S = ∑ r, U_r`. -/
theorem sum_remainder_sq {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) *
        ((∏ r, (1 + akvzScore P Q (x r)) - ∏ r, (1 - akvzScore P Q (x r))) / 2 -
          ∑ r, akvzScore P Q (x r)) ^ 2 =
      ((1 + akvzVar P Q) ^ k - (1 - akvzVar P Q) ^ k) / 2 - k * akvzVar P Q :=
  sum_prod_mul_remainder_sq (akvzMid P Q) (akvzScore P Q) (sum_akvzMid P Q)
    (sum_akvzMid_mul_akvzScore P Q) k

/-- **Step 2, series bound**: if `ρ = k · akvzVar P Q ≤ 1`, then `𝔼 (Φ - S)² ≤ ρ³ / 5`. -/
theorem sum_remainder_sq_le {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ)
    (hρ : k * akvzVar P Q ≤ 1) :
    ∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) *
        ((∏ r, (1 + akvzScore P Q (x r)) - ∏ r, (1 - akvzScore P Q (x r))) / 2 -
          ∑ r, akvzScore P Q (x r)) ^ 2 ≤ (k * akvzVar P Q) ^ 3 / 5 := by
  rw [sum_remainder_sq]
  exact oddPart_sub_le (akvzVar_nonneg P Q) hρ

/-- **Step 2, first absolute moment of the remainder**: `𝔼 |Φ - S| ≤ √(𝔼 (Φ - S)²)`, by the
Cauchy–Schwarz inequality for the probability weight `∏ r, M(x r)`. -/
theorem sum_abs_remainder_le_sqrt {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) *
        |(∏ r, (1 + akvzScore P Q (x r)) - ∏ r, (1 - akvzScore P Q (x r))) / 2 -
          ∑ r, akvzScore P Q (x r)| ≤
      √(∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) *
        ((∏ r, (1 + akvzScore P Q (x r)) - ∏ r, (1 - akvzScore P Q (x r))) / 2 -
          ∑ r, akvzScore P Q (x r)) ^ 2) :=
  sum_mul_abs_le_sqrt_sum_mul_sq _ _ _ (prod_akvzMid_nonneg P Q)
    (sum_prod_eq_one _ (sum_akvzMid P Q) k)

/-- **Step 2, first absolute moment of the remainder, explicit form**: if
`ρ = k · akvzVar P Q ≤ 1`, then `𝔼 |Φ - S| ≤ √(ρ³ / 5)`. -/
theorem sum_abs_remainder_le {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ)
    (hρ : k * akvzVar P Q ≤ 1) :
    ∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) *
        |(∏ r, (1 + akvzScore P Q (x r)) - ∏ r, (1 - akvzScore P Q (x r))) / 2 -
          ∑ r, akvzScore P Q (x r)| ≤ √((k * akvzVar P Q) ^ 3 / 5) :=
  (sum_abs_remainder_le_sqrt P Q k).trans (Real.sqrt_le_sqrt (sum_remainder_sq_le P Q k hρ))

/-- **Step 3, Hellinger-type lower bound for the total variation** ([AKVZ26, proof of
Theorem 1.1]):
`1 - e^{-k a / 2} ≤ d_TV(P^{⊗k}, Q^{⊗k})` with `a = akvzVar P Q`. -/
theorem one_sub_exp_le_tvDist_pi {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) :
    1 - Real.exp (-(k * akvzVar P Q) / 2) ≤
      tvDist (ProbabilityMeasure.pi fun _ : Fin k => P)
        (ProbabilityMeasure.pi fun _ : Fin k => Q) := by
  rw [tvDist_eq_one_sub_sum_min]
  have hmin : ∀ x : Fin k → α, min ((ProbabilityMeasure.pi fun _ : Fin k => P) {x} : ℝ)
      ((ProbabilityMeasure.pi fun _ : Fin k => Q) {x} : ℝ) =
      (∏ r, akvzMid P Q (x r)) *
        min (∏ r, (1 + akvzScore P Q (x r))) (∏ r, (1 - akvzScore P Q (x r))) := by
    intro x
    rw [coe_pi_apply_singleton_eq_mul_one_add P Q, coe_pi_apply_singleton_eq_mul_one_sub P Q,
      mul_min_of_nonneg _ _ (prod_akvzMid_nonneg P Q x)]
  rw [Finset.sum_congr rfl fun x _ => hmin x]
  have h := sum_prod_mul_min_le (akvzMid P Q) (akvzScore P Q) (akvzMid_nonneg P Q)
    (sum_akvzMid P Q) (abs_akvzScore_le_one P Q) k
  rw [← akvzVar] at h
  linarith

/-- **Step 3, lower bound for the score norm** ([AKVZ26, proof of Theorem 1.1]): `1 - e^{-k a / 2} ≤ A` with `a = akvzVar P Q` and
`A = akvzScoreNorm P Q k`. -/
theorem one_sub_exp_le_akvzScoreNorm {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) :
    1 - Real.exp (-(k * akvzVar P Q) / 2) ≤ akvzScoreNorm P Q k :=
  one_sub_exp_le_sum_prod_mul_sqrt (akvzMid P Q) (akvzScore P Q) (akvzMid_nonneg P Q)
    (sum_akvzMid P Q) (abs_akvzScore_le_one P Q) k

end Parking

end
