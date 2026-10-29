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

public import Parking.BorelTail
import Parking.SqrtSums

/-!
# Pointwise marginal bounds from the manuscript's Borel-tail argument

The zero-based `parkingG n j` denotes the source `g_n(j+1)`.
The providers `abs_parkingG_le_of_two_mul_le` and `parkingG_ge_of_le`
consume the endpoint-to-Borel-tail expansion in `Parking.BorelTail`.
Reflection extends the absolute bound to the right endpoint, and its cube is
summed to give `sum_abs_parkingG_pow_three_le` with the existing constant 6000.

The earlier midpoint lemmas `sum_parkingGap_le`, `le_sum_parkingGap`,
`neg_inv_le_parkingG_of_two_mul_le`, and `parkingG_le_of_two_mul_le` are retained
as alternative infrastructure. The reconstructed marginal providers below do
not use them.
-/

public section

namespace Parking

open Finset

/-! ### Sums of gaps in the left half -/

/-- Upper bound on a sum of gaps in the left half: if `2b ≤ n`, then
`∑_{a ≤ i < b} δ_n(i) ≤ 2 ∑_{a+1 ≤ I < b+1} I^{-3/2}` (`0`-based `i`). -/
theorem sum_parkingGap_le (n : ℕ) {a b : ℕ} (hb : 2 * b ≤ n) :
    ∑ i ∈ Ico a b, parkingGap n i ≤
      2 * ∑ I ∈ Ico (a + 1) (b + 1), 1 / ((I : ℝ) * √(I : ℝ)) := by
  rw [← sum_Ico_add' (fun I : ℕ => 1 / ((I : ℝ) * √(I : ℝ))) a b 1, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hib := (mem_Ico.1 hi).2
  have h := parkingGap_le (n := n) (i := i) (by omega)
  push_cast
  rw [mul_one_div]
  exact h

/-- Lower bound on a sum of gaps in the left half: if `2b ≤ n`, then
`(1/4) ∑_{a+1 ≤ I < b+1} I^{-3/2} ≤ ∑_{a ≤ i < b} δ_n(i)` (`0`-based `i`). -/
theorem le_sum_parkingGap (n : ℕ) {a b : ℕ} (hb : 2 * b ≤ n) :
    1 / 4 * ∑ I ∈ Ico (a + 1) (b + 1), 1 / ((I : ℝ) * √(I : ℝ)) ≤
      ∑ i ∈ Ico a b, parkingGap n i := by
  rw [← sum_Ico_add' (fun I : ℕ => 1 / ((I : ℝ) * √(I : ℝ))) a b 1, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hib := (mem_Ico.1 hi).2
  have h := le_parkingGap (n := n) (i := i) (by omega)
  push_cast
  calc 1 / 4 * (1 / (((i : ℝ) + 1) * √((i : ℝ) + 1))) =
        1 / (4 * ((i : ℝ) + 1) * √((i : ℝ) + 1)) := by
          rw [one_div_mul_one_div]
          congr 1
          ring
    _ ≤ parkingGap n i := h

/-! ### The left half `2j ≤ n` -/

/-- For `2j ≤ n` (`0`-based): `-1/(n + 1) ≤ g_n(j)`, since `g_n` is nonincreasing and
`g_n(m) ≥ -1/(n + 1)` at `m = ⌊n/2⌋`. -/
theorem neg_inv_le_parkingG_of_two_mul_le (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ)) : -1 / ((n : ℝ) + 1) ≤ parkingG n j := by
  have hmid := (parkingG_middle n hn).1
  have hle : parkingG n ⟨(n : ℕ) / 2, by omega⟩ ≤ parkingG n j :=
    parkingG_antitone n (show (j : ℕ) ≤ (n : ℕ) / 2 by omega)
  linarith

/-- For `2j ≤ n` (`0`-based): `g_n(j) ≤ 7/√(j + 1)`, by telescoping from `m = ⌊n/2⌋`:
`g_n(j) = g_n(m) + ∑_{j ≤ i < m} δ_n(i)`, with `g_n(m) ≤ (m+1)^{-3/2}` and
`∑_{j ≤ i < m} δ_n(i) ≤ 2 ((j+1)^{-3/2} + 2 (j+1)^{-1/2})`. -/
theorem parkingG_le_of_two_mul_le (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ)) : parkingG n j ≤ 7 / √((j : ℝ) + 1) := by
  have htel : parkingG n j = parkingG n ⟨(n : ℕ) / 2, by omega⟩ +
      ∑ i ∈ Ico (j : ℕ) ((n : ℕ) / 2), parkingGap n i :=
    parkingG_eq_add_sum n j ⟨(n : ℕ) / 2, by omega⟩ (show (j : ℕ) ≤ (n : ℕ) / 2 by omega)
  have hmid := (parkingG_middle n hn).2
  have hsum := sum_parkingGap_le (n : ℕ) (a := (j : ℕ)) (b := (n : ℕ) / 2) (by omega)
  have hS : ∑ I ∈ Ico ((j : ℕ) + 1) ((n : ℕ) / 2 + 1), 1 / ((I : ℝ) * √(I : ℝ)) ≤
      1 / (((j : ℝ) + 1) * √((j : ℝ) + 1)) + 2 / √((j : ℝ) + 1) := by
    have h := sum_inv_mul_sqrt_le (a := (j : ℕ) + 1) (by omega) ((n : ℕ) / 2 + 1)
    push_cast at h
    exact h
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith
  have hs0 : 0 < √((j : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
  have hM : (j : ℝ) + 1 ≤ (((n : ℕ) / 2 : ℕ) : ℝ) + 1 := by
    have : (j : ℕ) ≤ (n : ℕ) / 2 := by omega
    have : ((j : ℕ) : ℝ) ≤ (((n : ℕ) / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hsM : √((j : ℝ) + 1) ≤ ((((n : ℕ) / 2 : ℕ) : ℝ) + 1) * √((((n : ℕ) / 2 : ℕ) : ℝ) + 1) :=
    (Real.sqrt_le_sqrt hM).trans
      (le_mul_of_one_le_left (Real.sqrt_nonneg _) (hj1.trans hM))
  have h1 : 1 / ((((n : ℕ) / 2 : ℕ) + 1 : ℝ) * √(((n : ℕ) / 2 : ℕ) + 1 : ℝ)) ≤
      1 / √((j : ℝ) + 1) := one_div_le_one_div_of_le hs0 hsM
  have h2 : 1 / (((j : ℝ) + 1) * √((j : ℝ) + 1)) ≤ 1 / √((j : ℝ) + 1) :=
    one_div_le_one_div_of_le hs0 (le_mul_of_one_le_left hs0.le hj1)
  have h3 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have e1 : -1 / ((n : ℝ) + 1) = -(1 / ((n : ℝ) + 1)) := by ring
  have e2 : 2 / √((j : ℝ) + 1) = 2 * (1 / √((j : ℝ) + 1)) := by ring
  have e7 : 7 / √((j : ℝ) + 1) = 7 * (1 / √((j : ℝ) + 1)) := by ring
  linarith

/-- For `2j ≤ n` (`0`-based): `|g_n(j)| ≤ 7/√(j + 1)`, from the
endpoint-to-Borel-tail expansion. -/
theorem abs_parkingG_le_of_two_mul_le (n : ℕ+) (_hn : 2 ≤ (n : ℕ)) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ)) : |parkingG n j| ≤ 7 / √((j : ℝ) + 1) := by
  exact abs_parkingG_le_from_borelTail n j hj

/-! ### The right half `n ≤ 2j`, by reflection -/

/-- For `n ≤ 2j` (`0`-based): `|g_n(j)| ≤ 9/√(n - j)`. The reflection
`g_n(j) = -2/(n + 1) - g_n(n - j)` (`parkingG_add_parkingG_reflect`) brings the bound back to
the left half, where `2 (n - j) ≤ n`. -/
theorem abs_parkingG_le_of_le_two_mul (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n)
    (hj : (n : ℕ) ≤ 2 * (j : ℕ)) : |parkingG n j| ≤ 9 / √(((n : ℕ) - j : ℕ) : ℝ) := by
  have hj1 : 1 ≤ (j : ℕ) := by omega
  have hr := parkingG_add_parkingG_reflect n j hj1
  have hgk : |parkingG n ⟨(n : ℕ) - j, by omega⟩| ≤ 7 / √((((n : ℕ) - j : ℕ) : ℝ) + 1) :=
    abs_parkingG_le_of_two_mul_le n hn ⟨(n : ℕ) - j, by omega⟩
      (show 2 * ((n : ℕ) - j) ≤ (n : ℕ) by omega)
  obtain ⟨hk1, hk2⟩ := abs_le.1 hgk
  have hK1 : (1 : ℝ) ≤ (((n : ℕ) - j : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ (n : ℕ) - j by omega)
  have hKn : (((n : ℕ) - j : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by
    exact_mod_cast (show (n : ℕ) - j ≤ n by omega)
  have hs0 : 0 < √(((n : ℕ) - j : ℕ) : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsK : √(((n : ℕ) - j : ℕ) : ℝ) ≤ (((n : ℕ) - j : ℕ) : ℝ) :=
    Real.sqrt_le_self_iff.2 (Or.inr hK1)
  have h1 : 7 / √((((n : ℕ) - j : ℕ) : ℝ) + 1) ≤ 7 / √(((n : ℕ) - j : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hs0 (Real.sqrt_le_sqrt (by linarith))
  have h2 : 2 / ((n : ℝ) + 1) ≤ 2 / √(((n : ℕ) - j : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hs0 (by linarith)
  have h3 : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
  have h4 : 0 ≤ 2 / √(((n : ℕ) - j : ℕ) : ℝ) := by positivity
  have e1 : -2 / ((n : ℝ) + 1) = -(2 / ((n : ℝ) + 1)) := by ring
  have e9 : 9 / √(((n : ℕ) - j : ℕ) : ℝ) =
      2 / √(((n : ℕ) - j : ℕ) : ℝ) + 7 / √(((n : ℕ) - j : ℕ) : ℝ) := by ring
  rw [abs_le]
  constructor <;> linarith

/-! ### The three bounds of `lem:marginal` -/

/-- The absolute bound of `eq:g_bounds` (`lem:marginal`) with `C = 10`:
`|g_n(j + 1)| ≤ 10 / √(min (j + 1) (n - j))` for `n ≥ 2` (`0`-based `j`, so that
`min (j + 1) (n - j)` is the source `j ∧ (n + 1 - j)`). -/
theorem abs_parkingG_le (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n) :
    |parkingG n j| ≤ 10 / √((min ((j : ℕ) + 1) ((n : ℕ) - j) : ℕ) : ℝ) := by
  rcases le_or_gt ((j : ℕ) + 1) ((n : ℕ) - j) with h | h
  · rw [min_eq_left h]
    push_cast
    calc |parkingG n j| ≤ 7 / √((j : ℝ) + 1) :=
          abs_parkingG_le_of_two_mul_le n hn j (by omega)
      _ ≤ 10 / √((j : ℝ) + 1) := by gcongr; norm_num
  · rw [min_eq_right h.le]
    calc |parkingG n j| ≤ 9 / √(((n : ℕ) - j : ℕ) : ℝ) :=
          abs_parkingG_le_of_le_two_mul n hn j (by omega)
      _ ≤ 10 / √(((n : ℕ) - j : ℕ) : ℝ) := by gcongr; norm_num

/-- The positive lower bound of `lem:marginal` with `c = 1/25` and
`ε = 1/100`: `g_n(j + 1) ≥ 1 / (25 √(j + 1))` whenever `j + 1 ≤ max 1 ⌊n/100⌋` (`0`-based
`j`). For `j = 0` this is `g_n(1) = (n - 1)/(n + 1) ≥ 1/3`. Otherwise `100 (j + 1) ≤ n`, and
the Borel tail is at least `1/(2√(j+1))`, and the endpoint-telescoping error
is at most `1/(10√(j+1))`. -/
theorem parkingG_ge_of_le (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n)
    (hj : (j : ℕ) + 1 ≤ max 1 ((n : ℕ) / 100)) : 1 / (25 * √((j : ℝ) + 1)) ≤ parkingG n j := by
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
  · have hj0 : j = ⟨0, n.pos⟩ := Fin.ext h0
    have hjR : ((j : ℕ) : ℝ) = 0 := by exact_mod_cast h0
    rw [hjR, zero_add, Real.sqrt_one, mul_one, hj0, parkingG_zero]
    have hn2 : (2 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  · have h100 : 100 * ((j : ℕ) + 1) ≤ (n : ℕ) := by
      have : (j : ℕ) + 1 ≤ (n : ℕ) / 100 := by
        rcases le_total 1 ((n : ℕ) / 100) with h | h
        · rwa [max_eq_right h] at hj
        · rw [max_eq_left h] at hj
          omega
      omega
    have he := abs_parkingG_sub_borelTail_le n j (by omega)
    have htail := (borelTail_comparable (j := (j : ℕ) + 1) (by omega)).1
    simp only [Nat.cast_add, Nat.cast_one] at htail
    simp only [Nat.add_assoc] at he
    have ha : (2 : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast (show 2 ≤ (j : ℕ) + 1 by omega)
    have hs : (0 : ℝ) < √((j : ℝ) + 1) := by positivity
    have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hglobal : 6 * √((j : ℝ) + 1) / ((n : ℝ) + 1) ≤
        1 / (10 * √((j : ℝ) + 1)) := by
      rw [div_le_div_iff₀ hN (by positivity)]
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)
      have h100r : 100 * ((j : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast h100
      nlinarith
    have hcombine : 1 / (25 * √((j : ℝ) + 1)) +
        1 / (10 * √((j : ℝ) + 1)) ≤ 1 / (2 * √((j : ℝ) + 1)) := by
      field_simp
      nlinarith
    have hlo := (abs_le.1 he).1
    linarith

/-- If `0 ≤ x ≤ c/√a` with `0 < a`, then `x³ ≤ c³ · 1/(a √a)`. -/
theorem pow_three_le_of_le_div_sqrt {x c a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (h : x ≤ c / √a) :
    x ^ 3 ≤ c ^ 3 * (1 / (a * √a)) := by
  have h3 := pow_le_pow_left₀ hx h 3
  have hs : √a ^ 3 = a * √a := by rw [pow_succ, Real.sq_sqrt ha.le]
  rw [div_pow, hs] at h3
  rw [mul_one_div]
  exact h3

/-- The sum `∑_{j < n} (j + 1)^{-3/2}` is at most `3`. -/
theorem sum_fin_inv_mul_sqrt_le (n : ℕ) :
    ∑ j : Fin n, 1 / ((((j : ℕ) + 1 : ℕ) : ℝ) * √(((j : ℕ) + 1 : ℕ) : ℝ)) ≤ 3 := by
  rw [Fin.sum_univ_eq_sum_range
      (fun j => 1 / ((((j + 1 : ℕ)) : ℝ) * √((j + 1 : ℕ) : ℝ))) n, range_eq_Ico,
    sum_Ico_add' (fun I : ℕ => 1 / ((I : ℝ) * √(I : ℝ))) 0 n 1, zero_add]
  have h := sum_inv_mul_sqrt_le (a := 1) le_rfl (n + 1)
  simp only [Nat.cast_one, Real.sqrt_one, mul_one, div_one] at h
  linarith

/-- The cubic estimate of `eq:g_moments` (`lem:marginal`): `∑_j |g_n(j)|³ ≤ 6000` for
`n ≥ 2`. By `abs_parkingG_le`, `|g_n(j + 1)|³ ≤ 1000 ((j+1)^{-3/2} + (n-j)^{-3/2})`, and
both sums are at most `∑_{I ≥ 1} I^{-3/2} ≤ 3`. -/
theorem sum_abs_parkingG_pow_three_le (n : ℕ+) (hn : 2 ≤ (n : ℕ)) :
    ∑ j, |parkingG n j| ^ 3 ≤ 6000 := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun I : ℕ => 1 / ((I : ℝ) * √(I : ℝ)) := ⟨_, rfl⟩
  have hf0 : ∀ I, 0 ≤ f I := fun I => by
    simp only [hf]
    positivity
  have hterm : ∀ j : Fin n, |parkingG n j| ^ 3 ≤ 1000 * (f ((j : ℕ) + 1) + f ((n : ℕ) - j)) := by
    intro j
    obtain ⟨M, hM⟩ : ∃ M, M = min ((j : ℕ) + 1) ((n : ℕ) - j) := ⟨_, rfl⟩
    have hM0 : 0 < M := by
      rw [hM]
      exact lt_min (by omega) (by omega)
    have hb := abs_parkingG_le n hn j
    rw [← hM] at hb
    have h := pow_three_le_of_le_div_sqrt (abs_nonneg _) (by exact_mod_cast hM0) hb
    have hfM : f M ≤ f ((j : ℕ) + 1) + f ((n : ℕ) - j) := by
      rcases min_choice ((j : ℕ) + 1) ((n : ℕ) - j) with h' | h'
      · rw [hM, h']
        exact le_add_of_nonneg_right (hf0 _)
      · rw [hM, h']
        exact le_add_of_nonneg_left (hf0 _)
    calc |parkingG n j| ^ 3 ≤ 10 ^ 3 * (1 / ((M : ℝ) * √(M : ℝ))) := h
      _ = 1000 * f M := by
        simp only [hf]
        norm_num
      _ ≤ 1000 * (f ((j : ℕ) + 1) + f ((n : ℕ) - j)) := by gcongr
  have hS : ∑ j : Fin n, f ((j : ℕ) + 1) ≤ 3 := by
    simp only [hf]
    exact sum_fin_inv_mul_sqrt_le n
  calc ∑ j, |parkingG n j| ^ 3 ≤ ∑ j : Fin n, 1000 * (f ((j : ℕ) + 1) + f ((n : ℕ) - j)) :=
        sum_le_sum fun j _ => hterm j
    _ = 1000 * (∑ j : Fin n, f ((j : ℕ) + 1) + ∑ j : Fin n, f ((n : ℕ) - j)) := by
        rw [← mul_sum, sum_add_distrib]
    _ = 2000 * ∑ j : Fin n, f ((j : ℕ) + 1) := by
        rw [sum_fin_reflect f]
        ring
    _ ≤ 2000 * 3 := mul_le_mul_of_nonneg_left hS (by norm_num)
    _ = 6000 := by norm_num

end Parking

end
