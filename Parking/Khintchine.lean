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
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev

/-!
# Khintchine's inequality with exponent one

This module depends on Mathlib only.

Fix `a : Fin k → ℝ`. A sign pattern is `ε : Fin k → Bool`, the sign of coordinate `r` being
`+1` when `ε r` holds and `-1` otherwise, so that the signed sum is
`∑ r, (if ε r then a r else -a r)`. Averaging over the `2 ^ k` sign patterns is the
expectation `𝔼_ε` for independent uniform signs. The main result is Khintchine's inequality
with exponent one (`khintchine_one`):

$$
\frac{\lVert a\rVert_2}{\sqrt3}\le\mathbb E_\varepsilon\Bigl\lvert\sum_r\varepsilon_ra_r\Bigr\rvert
\le\lVert a\rVert_2 .
$$

The proof avoids fractional powers.

* The second moment `∑ ε, (∑ r, ε_r a_r)² = 2 ^ k ∑ a²` (`sum_sq_sum_ite_neg`) and the fourth
  moment `∑ ε, (∑ r, ε_r a_r)⁴ = 2 ^ k (3 (∑ a²)² - 2 ∑ a⁴)` (`sum_pow_four_sum_ite_neg`) are
  computed by induction on `k`. Hence `𝔼 (∑ ε a)⁴ ≤ 3 (∑ a²)²`
  (`sum_pow_four_sum_ite_neg_div_le`).
* The weighted finite Hölder inequality `(𝔼 X²)³ ≤ (𝔼 |X|)² 𝔼 X⁴`
  (`sum_mul_sq_pow_three_le`), the root-free form of
  `𝔼 |X| ≥ (𝔼 X²)^{3/2} / (𝔼 X⁴)^{1/2}`, follows from two weighted Cauchy–Schwarz steps
  (`sq_sum_mul_mul_le`).
* Together they give the root-free lower bound `∑ a² ≤ 3 (𝔼 |∑ ε a|)²`
  (`sum_sq_le_three_mul_sq_avg_abs`). The upper bound `(𝔼 |∑ ε a|)² ≤ ∑ a²`
  (`sq_avg_abs_le_sum_sq`) is Cauchy–Schwarz.
-/

public section

namespace Parking

open Finset

/-! ### Weighted Cauchy–Schwarz and Hölder inequalities -/

/-- Weighted Cauchy–Schwarz inequality for finite sums, without square roots: for nonnegative
weights `w`, `(∑ w f g)² ≤ (∑ w f²) (∑ w g²)`. -/
theorem sq_sum_mul_mul_le {ι : Type*} (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i * g i) ^ 2 ≤ (∑ i ∈ s, w i * f i ^ 2) * ∑ i ∈ s, w i * g i ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
    (fun i _ => le_of_eq (by ring))

/-- **Weighted finite Hölder inequality** between the first, second and fourth moments, in
root-free form: for nonnegative weights `w`, `(∑ w X²)³ ≤ (∑ w |X|)² ∑ w X⁴`. For probability
weights this is `𝔼 |X| ≥ (𝔼 X²)^{3/2} / (𝔼 X⁴)^{1/2}`. -/
theorem sum_mul_sq_pow_three_le {ι : Type*} (s : Finset ι) (w X : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * X i ^ 2) ^ 3 ≤ (∑ i ∈ s, w i * |X i|) ^ 2 * ∑ i ∈ s, w i * X i ^ 4 := by
  set E1 := ∑ i ∈ s, w i * |X i| with hE1
  set E2 := ∑ i ∈ s, w i * X i ^ 2 with hE2
  set E3 := ∑ i ∈ s, w i * |X i| * X i ^ 2 with hE3
  set E4 := ∑ i ∈ s, w i * X i ^ 4 with hE4
  -- First Cauchy–Schwarz step, with weights `w |X|`: `(𝔼 X²)² ≤ 𝔼 |X| 𝔼 |X|³`.
  have h1 : E2 ^ 2 ≤ E1 * E3 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i hi => mul_nonneg (hw i hi) (abs_nonneg _))
      (fun i hi => mul_nonneg (mul_nonneg (hw i hi) (abs_nonneg _)) (sq_nonneg _))
      (fun i _ => le_of_eq (by
        rw [show w i * |X i| * (w i * |X i| * X i ^ 2) = w i ^ 2 * |X i| ^ 2 * X i ^ 2 by ring,
          sq_abs]
        ring))
  -- Second Cauchy–Schwarz step, with weights `w`: `(𝔼 |X|³)² ≤ 𝔼 X² 𝔼 X⁴`.
  have h2 : E3 ^ 2 ≤ E2 * E4 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
      (fun i hi => mul_nonneg (hw i hi) (by positivity))
      (fun i _ => le_of_eq (by
        rw [show (w i * |X i| * X i ^ 2) ^ 2 = w i ^ 2 * |X i| ^ 2 * X i ^ 4 by ring, sq_abs]
        ring))
  have h4 : E2 ^ 3 * E2 ≤ (E1 ^ 2 * E4) * E2 :=
    calc E2 ^ 3 * E2 = (E2 ^ 2) ^ 2 := by ring
      _ ≤ (E1 * E3) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
      _ = E1 ^ 2 * E3 ^ 2 := mul_pow _ _ _
      _ ≤ E1 ^ 2 * (E2 * E4) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = (E1 ^ 2 * E4) * E2 := by ring
  have hE2nonneg : 0 ≤ E2 := Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hE4nonneg : 0 ≤ E4 := Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (by positivity)
  rcases hE2nonneg.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · exact le_of_mul_le_mul_right h4 hpos

/-! ### Moments of signed sums -/

/-- The sum over sign patterns of length `k + 1`, split according to the first sign. -/
theorem sum_pi_fin_succ_bool {M : Type*} [AddCommMonoid M] {k : ℕ}
    (f : (Fin (k + 1) → Bool) → M) :
    ∑ ε : Fin (k + 1) → Bool, f ε =
      ∑ ε : Fin k → Bool, (f (Fin.cons true ε) + f (Fin.cons false ε)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.sum_add_distrib]
  rfl

/-- A constant summed over the `2 ^ k` sign patterns. -/
theorem sum_const_pi_fin_bool {k : ℕ} (c : ℝ) : ∑ _ε : Fin k → Bool, c = 2 ^ k * c := by
  simp

/-- The signed sum of a tuple of length `k + 1`, split according to the first sign. -/
theorem sum_ite_neg_cons {k : ℕ} (a : Fin (k + 1) → ℝ) (b : Bool) (ε : Fin k → Bool) :
    ∑ r, (if (Fin.cons b ε : Fin (k + 1) → Bool) r then a r else -a r) =
      (if b then a 0 else -a 0) + ∑ r : Fin k, (if ε r then a r.succ else -a r.succ) := by
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- **Second moment of a Rademacher sum**: `∑ ε, (∑ r, ε_r a_r)² = 2 ^ k ∑ r, a_r²`. -/
theorem sum_sq_sum_ite_neg {k : ℕ} (a : Fin k → ℝ) :
    ∑ ε : Fin k → Bool, (∑ r, (if ε r then a r else -a r)) ^ 2 = 2 ^ k * ∑ r, a r ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := ih fun r => a r.succ
    rw [sum_pi_fin_succ_bool]
    simp only [sum_ite_neg_cons, ↓reduceIte, Bool.false_eq_true]
    rw [Fin.sum_univ_succ]
    calc _ = ∑ ε : Fin k → Bool, (2 * a 0 ^ 2 +
          2 * (∑ r : Fin k, (if ε r then a r.succ else -a r.succ)) ^ 2) :=
          Finset.sum_congr rfl fun ε _ => by ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h, sum_const_pi_fin_bool]
          ring

/-- **Fourth moment of a Rademacher sum**:
`∑ ε, (∑ r, ε_r a_r)⁴ = 2 ^ k (3 (∑ r, a_r²)² - 2 ∑ r, a_r⁴)`. -/
theorem sum_pow_four_sum_ite_neg {k : ℕ} (a : Fin k → ℝ) :
    ∑ ε : Fin k → Bool, (∑ r, (if ε r then a r else -a r)) ^ 4 =
      2 ^ k * (3 * (∑ r, a r ^ 2) ^ 2 - 2 * ∑ r, a r ^ 4) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 := sum_sq_sum_ite_neg fun r => a r.succ
    have h4 := ih fun r => a r.succ
    rw [sum_pi_fin_succ_bool]
    simp only [sum_ite_neg_cons, ↓reduceIte, Bool.false_eq_true]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    calc _ = ∑ ε : Fin k → Bool, (2 * a 0 ^ 4 +
          12 * a 0 ^ 2 * (∑ r : Fin k, (if ε r then a r.succ else -a r.succ)) ^ 2 +
          2 * (∑ r : Fin k, (if ε r then a r.succ else -a r.succ)) ^ 4) :=
          Finset.sum_congr rfl fun ε _ => by ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h2, h4, sum_const_pi_fin_bool]
          ring

/-- **Fourth-moment bound**: `𝔼_ε (∑ r, ε_r a_r)⁴ ≤ 3 (∑ r, a_r²)²`, the expectation being
the average over the `2 ^ k` sign patterns. -/
theorem sum_pow_four_sum_ite_neg_div_le {k : ℕ} (a : Fin k → ℝ) :
    (∑ ε : Fin k → Bool, (∑ r, (if ε r then a r else -a r)) ^ 4) / 2 ^ k ≤
      3 * (∑ r, a r ^ 2) ^ 2 := by
  have hT : 0 ≤ ∑ r, a r ^ 4 := Finset.sum_nonneg fun r _ => by positivity
  rw [sum_pow_four_sum_ite_neg, mul_div_cancel_left₀ _ (by positivity)]
  linarith

/-! ### Khintchine's inequality -/

/-- **Khintchine's inequality for `p = 1`, lower bound in root-free form**:
`∑ r, a_r² ≤ 3 (𝔼_ε |∑ r, ε_r a_r|)²`. -/
theorem sum_sq_le_three_mul_sq_avg_abs {k : ℕ} (a : Fin k → ℝ) :
    ∑ r, a r ^ 2 ≤
      3 * ((∑ ε : Fin k → Bool, |∑ r, (if ε r then a r else -a r)|) / 2 ^ k) ^ 2 := by
  have hH := sum_mul_sq_pow_three_le Finset.univ (fun _ => (1 : ℝ))
    (fun ε : Fin k → Bool => ∑ r, (if ε r then a r else -a r)) fun _ _ => zero_le_one
  simp only [one_mul] at hH
  rw [sum_sq_sum_ite_neg, sum_pow_four_sum_ite_neg] at hH
  set S := ∑ r, a r ^ 2 with hS
  set T := ∑ r, a r ^ 4 with hT
  set E := ∑ ε : Fin k → Bool, |∑ r, (if ε r then a r else -a r)| with hE
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun r _ => by positivity
  rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    positivity
  · have key : (S * (2 ^ k) ^ 2) * (2 ^ k * S ^ 2) ≤ (3 * E ^ 2) * (2 ^ k * S ^ 2) :=
      calc (S * (2 ^ k) ^ 2) * (2 ^ k * S ^ 2) = (2 ^ k * S) ^ 3 := by ring
        _ ≤ E ^ 2 * (2 ^ k * (3 * S ^ 2 - 2 * T)) := hH
        _ ≤ E ^ 2 * (2 ^ k * (3 * S ^ 2)) := by gcongr; linarith
        _ = (3 * E ^ 2) * (2 ^ k * S ^ 2) := by ring
    exact le_of_mul_le_mul_right key (by positivity)

/-- **Khintchine's inequality for `p = 1`, upper bound in root-free form**:
`(𝔼_ε |∑ r, ε_r a_r|)² ≤ ∑ r, a_r²`. -/
theorem sq_avg_abs_le_sum_sq {k : ℕ} (a : Fin k → ℝ) :
    ((∑ ε : Fin k → Bool, |∑ r, (if ε r then a r else -a r)|) / 2 ^ k) ^ 2 ≤
      ∑ r, a r ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k → Bool)))
    (f := fun ε => |∑ r, (if ε r then a r else -a r)|)
  simp only [sq_abs] at h
  rw [sum_sq_sum_ite_neg] at h
  have hcard : ((Finset.univ : Finset (Fin k → Bool)).card : ℝ) = 2 ^ k := by simp
  rw [hcard] at h
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **Khintchine's inequality for `p = 1`**: for `a : Fin k → ℝ`, with the expectation over
independent uniform signs written as the average over the `2 ^ k` sign patterns,
`‖a‖₂ / √3 ≤ 𝔼_ε |∑ r, ε_r a_r| ≤ ‖a‖₂`. -/
theorem khintchine_one {k : ℕ} (a : Fin k → ℝ) :
    √(∑ r, a r ^ 2) / √3 ≤ (∑ ε : Fin k → Bool, |∑ r, (if ε r then a r else -a r)|) / 2 ^ k ∧
      (∑ ε : Fin k → Bool, |∑ r, (if ε r then a r else -a r)|) / 2 ^ k ≤ √(∑ r, a r ^ 2) := by
  set m := (∑ ε : Fin k → Bool, |∑ r, (if ε r then a r else -a r)|) / 2 ^ k with hm_def
  have hm : 0 ≤ m := div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
  constructor
  · rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
    calc √(∑ r, a r ^ 2) ≤ √(3 * m ^ 2) := Real.sqrt_le_sqrt (sum_sq_le_three_mul_sq_avg_abs a)
      _ = m * √3 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hm, mul_comm]
  · exact (le_abs_self _).trans (Real.abs_le_sqrt (sq_avg_abs_le_sum_sq a))

/-- Khintchine's lower bound in the multiplied form used for symmetrization:
`‖a‖₂ ≤ √3 𝔼_ε |∑ r, ε_r a_r|`. -/
theorem sqrt_sum_sq_le_sqrt_three_mul {k : ℕ} (a : Fin k → ℝ) :
    √(∑ r, a r ^ 2) ≤
      √3 * ((∑ ε : Fin k → Bool, |∑ r, (if ε r then a r else -a r)|) / 2 ^ k) := by
  have h := (khintchine_one a).1
  rwa [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)), mul_comm] at h

end Parking
