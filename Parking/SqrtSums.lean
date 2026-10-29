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

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Telescoped bounds on sums of negative powers of integers

This module collects the elementary bounds on
sums over integer intervals `[a, b)` used in the estimates of the source paper:

* `2 / √a - 2 / √b ≤ ∑_{a ≤ I < b} 1 / (I √I) ≤ 1 / (a √a) + 2 / √a`
  (`sub_le_sum_inv_mul_sqrt`, `sum_inv_mul_sqrt_le`);
* `∑_{a ≤ I < b} 1 / (I² √I) ≤ 2 / (a √a)` (`sum_inv_sq_mul_sqrt_le`);
* `∑_{1 ≤ I < b} 1 / √I ≤ 2 √b` (`sum_inv_sqrt_le`);
* `log (n + 1) ≤ ∑_{j < n} 1 / (j + 1) ≤ 1 + log n` (`log_add_one_le_sum_inv`,
  `sum_inv_le_one_add_log`), from the harmonic-number bounds of Mathlib;
* the reflection `∑_{j < n} f (n - j) = ∑_{j < n} f (j + 1)` (`sum_fin_reflect`).

Every interval bound follows from a per-term telescoping inequality
(`sum_Ico_le_sub_of_le`, `sub_le_sum_Ico_of_le`). The per-term inequalities are proved for a
real variable `x`, by writing `√x` and `√(x + 1)` as two positive reals `s < t` with
`t² - s² = 1`.
-/

public section

namespace Parking

open Finset

/-! ### Telescoping -/

/-- Telescoping upper bound: if `f I ≤ g (I + 1) - g I` for every `I ∈ [a, b)`, then
`∑_{a ≤ I < b} f I ≤ g b - g a`. -/
theorem sum_Ico_le_sub_of_le {f g : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ I, a ≤ I → I < b → f I ≤ g (I + 1) - g I) :
    ∑ I ∈ Ico a b, f I ≤ g b - g a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab]
    have h₁ := ih fun I h₁ h₂ => h I h₁ (by omega)
    have h₂ := h b hab (by omega)
    linarith

/-- Telescoping lower bound: if `g (I + 1) - g I ≤ f I` for every `I ∈ [a, b)`, then
`g b - g a ≤ ∑_{a ≤ I < b} f I`. -/
theorem sub_le_sum_Ico_of_le {f g : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ I, a ≤ I → I < b → g (I + 1) - g I ≤ f I) :
    g b - g a ≤ ∑ I ∈ Ico a b, f I := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab]
    have h₁ := ih fun I h₁ h₂ => h I h₁ (by omega)
    have h₂ := h b hab (by omega)
    linarith

/-! ### Per-term inequalities -/

/-- If `0 ≤ x`, then `(√(x + 1) - √x) (√(x + 1) + √x) = 1`. -/
theorem sqrt_add_one_sub_sqrt_mul (x : ℝ) (hx : 0 ≤ x) :
    (√(x + 1) - √x) * (√(x + 1) + √x) = 1 := by
  have hs : √x ^ 2 = x := Real.sq_sqrt hx
  have ht : √(x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  nlinarith

/-- The lower telescoping inequality for `1 / (x √x)`: if `0 < x`, then
`2 / √x - 2 / √(x + 1) ≤ 1 / (x √x)`. -/
theorem two_div_sqrt_sub_le_inv_mul_sqrt {x : ℝ} (hx : 0 < x) :
    2 / √x - 2 / √(x + 1) ≤ 1 / (x * √x) := by
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  have ht : 0 < √(x + 1) := Real.sqrt_pos.2 (by linarith)
  have hst : √x ≤ √(x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hs2 : √x ^ 2 = x := Real.sq_sqrt hx.le
  have key := sqrt_add_one_sub_sqrt_mul x hx.le
  rw [div_sub_div _ _ hs.ne' ht.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  -- `2 (t - s) s³ ≤ s t`, from `(t - s) (t + s) = 1` and `2 s ≤ t + s`.
  nlinarith [mul_pos hs ht, mul_pos hs hs, mul_nonneg (mul_nonneg hs.le hs.le) (sub_nonneg.2 hst)]

/-- The upper telescoping inequality for `1 / (x √x)`, at `x + 1`: if `0 < x`, then
`1 / ((x + 1) √(x + 1)) ≤ 2 / √x - 2 / √(x + 1)`. -/
theorem inv_mul_sqrt_le_two_div_sqrt_sub {x : ℝ} (hx : 0 < x) :
    1 / ((x + 1) * √(x + 1)) ≤ 2 / √x - 2 / √(x + 1) := by
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  have ht : 0 < √(x + 1) := Real.sqrt_pos.2 (by linarith)
  have hst : √x ≤ √(x + 1) := Real.sqrt_le_sqrt (by linarith)
  have ht2 : √(x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have key := sqrt_add_one_sub_sqrt_mul x hx.le
  rw [div_sub_div _ _ hs.ne' ht.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  -- `s t ≤ 2 (t - s) t³`, from `(t - s) (t + s) = 1` and `t + s ≤ 2 t`.
  nlinarith [mul_pos hs ht, mul_pos ht ht, mul_nonneg (mul_nonneg ht.le ht.le) (sub_nonneg.2 hst)]

/-- The telescoping inequality for `1 / (x² √x)`: if `1 ≤ x`, then
`1 / (x² √x) ≤ 2 / (x √x) - 2 / ((x + 1) √(x + 1))`. -/
theorem inv_sq_mul_sqrt_le_sub {x : ℝ} (hx : 1 ≤ x) :
    1 / (x ^ 2 * √x) ≤ 2 / (x * √x) - 2 / ((x + 1) * √(x + 1)) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.2 hx0
  have ht : 0 < √(x + 1) := Real.sqrt_pos.2 (by linarith)
  have hs2 : √x ^ 2 = x := Real.sq_sqrt hx0.le
  have ht2 : √(x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  -- `2 x² √x ≤ (2 x - 1) (x + 1) √(x + 1)`, by squaring.
  have key : 2 * x ^ 2 * √x ≤ (2 * x - 1) * (x + 1) * √(x + 1) := by
    have h2x : 0 ≤ 2 * x - 1 := by linarith
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow (2 * x ^ 2), mul_pow ((2 * x - 1) * (x + 1)), hs2, ht2]
    have h₁ : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
    have h₂ : x ≤ x ^ 3 := le_self_pow₀ hx (by norm_num)
    nlinarith
  rw [div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h₃ : 0 ≤ x * √x * ((2 * x - 1) * (x + 1) * √(x + 1) - 2 * x ^ 2 * √x) :=
    mul_nonneg (by positivity) (sub_nonneg.2 key)
  nlinarith

/-- The telescoping inequality for `1 / x²`: if `1 ≤ x`, then `1 / x² ≤ 2 / x - 2 / (x + 1)`. -/
theorem inv_sq_le_two_div_sub {x : ℝ} (hx : 1 ≤ x) : 1 / x ^ 2 ≤ 2 / x - 2 / (x + 1) := by
  have hx0 : 0 < x := by linarith
  rw [div_sub_div _ _ hx0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The telescoping inequality for `1 / √x`: if `1 ≤ x`, then `1 / √x ≤ 2 √x - 2 √(x - 1)`. -/
theorem inv_sqrt_le_two_mul_sqrt_sub {x : ℝ} (hx : 1 ≤ x) :
    1 / √x ≤ 2 * √x - 2 * √(x - 1) := by
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hr : √(x - 1) ≤ √x := Real.sqrt_le_sqrt (by linarith)
  have key := sqrt_add_one_sub_sqrt_mul (x - 1) (by linarith)
  rw [sub_add_cancel] at key
  rw [div_le_iff₀ hs]
  -- `1 = (s - r) (s + r) ≤ 2 (s - r) s`.
  nlinarith [Real.sqrt_nonneg (x - 1)]

/-! ### Sums over integer intervals -/

/-- Lower bound by telescoping: if `1 ≤ a ≤ b`, then
`2 / √a - 2 / √b ≤ ∑_{a ≤ I < b} 1 / (I √I)`. -/
theorem sub_le_sum_inv_mul_sqrt {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    2 / √(a : ℝ) - 2 / √(b : ℝ) ≤ ∑ I ∈ Finset.Ico a b, 1 / ((I : ℝ) * √(I : ℝ)) := by
  have htel := sub_le_sum_Ico_of_le (f := fun I : ℕ => 1 / ((I : ℝ) * √(I : ℝ)))
    (g := fun I : ℕ => -(2 / √(I : ℝ))) hab fun I hI _ => by
      have hI0 : (0 : ℝ) < I := by exact_mod_cast (show 0 < I by omega)
      have hterm := two_div_sqrt_sub_le_inv_mul_sqrt hI0
      push_cast
      linarith
  linarith

/-- Upper bound by telescoping: if `1 ≤ a`, then
`∑_{a ≤ I < b} 1 / (I √I) ≤ 1 / (a √a) + 2 / √a`. -/
theorem sum_inv_mul_sqrt_le {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    ∑ I ∈ Finset.Ico a b, 1 / ((I : ℝ) * √(I : ℝ)) ≤
      1 / ((a : ℝ) * √(a : ℝ)) + 2 / √(a : ℝ) := by
  rcases lt_or_ge a b with hab | hab
  · rw [sum_eq_sum_Ico_succ_bot hab]
    have htel := sum_Ico_le_sub_of_le (f := fun I : ℕ => 1 / ((I : ℝ) * √(I : ℝ)))
      (g := fun I : ℕ => -(2 / √((I : ℝ) - 1))) (show a + 1 ≤ b from hab) fun I hI _ => by
        have hI0 : (0 : ℝ) < (I : ℝ) - 1 := by
          have hI2 : (2 : ℝ) ≤ I := by exact_mod_cast (show 2 ≤ I by omega)
          linarith
        have hterm := inv_mul_sqrt_le_two_div_sqrt_sub hI0
        rw [sub_add_cancel] at hterm
        push_cast
        rw [add_sub_cancel_right]
        linarith
    push_cast at htel
    rw [add_sub_cancel_right] at htel
    have hb : 0 ≤ 2 / √((b : ℝ) - 1) := by positivity
    linarith
  · rw [Ico_eq_empty_of_le hab, sum_empty]
    positivity

/-- Upper bound by telescoping: if `1 ≤ a`, then `∑_{a ≤ I < b} 1 / (I² √I) ≤ 2 / (a √a)`. -/
theorem sum_inv_sq_mul_sqrt_le {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    ∑ I ∈ Finset.Ico a b, 1 / ((I : ℝ) ^ 2 * √(I : ℝ)) ≤ 2 / ((a : ℝ) * √(a : ℝ)) := by
  rcases le_or_gt a b with hab | hab
  · have htel := sum_Ico_le_sub_of_le (f := fun I : ℕ => 1 / ((I : ℝ) ^ 2 * √(I : ℝ)))
      (g := fun I : ℕ => -(2 / ((I : ℝ) * √(I : ℝ)))) hab fun I hI _ => by
        have hI1 : (1 : ℝ) ≤ I := by exact_mod_cast (show 1 ≤ I by omega)
        have hterm := inv_sq_mul_sqrt_le_sub hI1
        push_cast
        linarith
    have hb : 0 ≤ 2 / ((b : ℝ) * √(b : ℝ)) := by positivity
    linarith
  · rw [Ico_eq_empty_of_le hab.le, sum_empty]
    positivity

/-- Upper bound by telescoping: if `1 ≤ a`, then `∑_{a ≤ I < b} 1 / I² ≤ 2 / a`. -/
theorem sum_inv_sq_le {a : ℕ} (ha : 1 ≤ a) (b : ℕ) :
    ∑ I ∈ Finset.Ico a b, 1 / (I : ℝ) ^ 2 ≤ 2 / (a : ℝ) := by
  rcases le_or_gt a b with hab | hab
  · have htel := sum_Ico_le_sub_of_le (f := fun I : ℕ => 1 / (I : ℝ) ^ 2)
      (g := fun I : ℕ => -(2 / (I : ℝ))) hab fun I hI _ => by
        have hI1 : (1 : ℝ) ≤ I := by exact_mod_cast (show 1 ≤ I by omega)
        have hterm := inv_sq_le_two_div_sub hI1
        push_cast
        linarith
    have hb : 0 ≤ 2 / (b : ℝ) := by positivity
    linarith
  · rw [Ico_eq_empty_of_le hab.le, sum_empty]
    positivity

/-- Upper bound by telescoping: `∑_{1 ≤ I < b} 1 / √I ≤ 2 √b`. -/
theorem sum_inv_sqrt_le (b : ℕ) : ∑ I ∈ Finset.Ico 1 b, 1 / √(I : ℝ) ≤ 2 * √(b : ℝ) := by
  rcases le_or_gt 1 b with hb | hb
  · have htel := sum_Ico_le_sub_of_le (f := fun I : ℕ => 1 / √(I : ℝ))
      (g := fun I : ℕ => 2 * √((I : ℝ) - 1)) hb fun I hI _ => by
        have hI1 : (1 : ℝ) ≤ I := by exact_mod_cast hI
        have hterm := inv_sqrt_le_two_mul_sqrt_sub hI1
        push_cast
        rw [add_sub_cancel_right]
        linarith
    simp only [Nat.cast_one, sub_self, Real.sqrt_zero, mul_zero, sub_zero] at htel
    have hsq : √((b : ℝ) - 1) ≤ √(b : ℝ) := Real.sqrt_le_sqrt (by linarith)
    linarith
  · rw [Ico_eq_empty_of_le hb.le, sum_empty]
    positivity

/-! ### Reflection and harmonic sums -/

/-- Reflection of a sum over `Fin n`: `∑_{j < n} f (n - j) = ∑_{j < n} f (j + 1)`. -/
theorem sum_fin_reflect {n : ℕ} (f : ℕ → ℝ) : ∑ j : Fin n, f (n - j) = ∑ j : Fin n, f (j + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => f (n - j)) n,
    Fin.sum_univ_eq_sum_range (fun j => f (j + 1)) n,
    ← sum_range_reflect (fun j => f (j + 1)) n]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  congr 1
  omega

/-- The sum `∑_{j < n} 1 / (j + 1)` is the harmonic number `H_n`, cast to `ℝ`. -/
theorem sum_fin_inv_eq_harmonic (n : ℕ) : ∑ j : Fin n, 1 / ((j : ℝ) + 1) = harmonic n := by
  rw [Fin.sum_univ_eq_sum_range (fun j => 1 / ((j : ℝ) + 1)) n, harmonic]
  push_cast
  simp only [one_div]

/-- Lower bound of the harmonic sum: `log (n + 1) ≤ ∑_{j < n} 1 / (j + 1)`. -/
theorem log_add_one_le_sum_inv (n : ℕ) : Real.log (n + 1) ≤ ∑ j : Fin n, 1 / ((j : ℝ) + 1) := by
  rw [sum_fin_inv_eq_harmonic]
  exact_mod_cast log_add_one_le_harmonic n

/-- Upper bound of the harmonic sum: `∑_{j < n} 1 / (j + 1) ≤ 1 + log n`. -/
theorem sum_inv_le_one_add_log (n : ℕ) : ∑ j : Fin n, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log n := by
  rw [sum_fin_inv_eq_harmonic]
  exact harmonic_le_one_add_log n

end Parking
