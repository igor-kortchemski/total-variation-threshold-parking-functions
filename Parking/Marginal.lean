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

public import Parking.BorelAsymptotics
public import Parking.FirstCoordCount
import Parking.Count

/-!
# Exact identities for the marginal correction `g_n`

This module proves the exact identities behind
`lem:marginal` for the marginal correction

`g_n(j) = n μ_n(j) - 1` (`lem:marginal`),

where `μ_n` is the law of the first coordinate of a uniform parking function of size `n`.
The value `j : Fin n` is `0`-based: `parkingG n j` is the source `g_n(j + 1)`, and
`parkingGap n i = q_{i+1} q_{n-i} / q_{n+1}` is the source `δ_n(i + 1)`.

* `n μ_n(j) = n N(j) / (n + 1)^(n - 1)`, with `N(j) = firstValueCount (n - 1) j`
  (`one_add_parkingG`), and `n · gapCount (n - 1) i / (n + 1)^(n - 1) = q_{i+1} q_{n-i} /
  q_{n+1}` (`parkingGap_eq_gapCount`): the exponentials cancel and the factorials give the
  binomial coefficient. With [DH17, Corollary 1] (`firstValueCount_eq_add`), this gives
  `g_n(j) - g_n(j + 1) = δ_n(j)` (`parkingG_sub_parkingG_succ`, `lem:marginal`), hence the
  monotonicity of `g_n` (`parkingG_antitone`).
* The endpoint values `g_n(1) = (n - 1)/(n + 1)` and `1 + g_n(n) = (n/(n + 1))^(n - 1) =
  δ_n(1)` (`parkingG_zero`, `one_add_parkingG_last`, `lem:marginal`), hence
  `e^{-1} ≤ 1 + g_n ≤ 2` (`exp_neg_one_le_one_add_parkingG`, `one_add_parkingG_le_two`).
* The reflection `g_n(j) + g_n(n + 2 - j) = -2/(n + 1)` (`parkingG_add_parkingG_reflect`,
  `eq:marginal_reflection`, `lem:marginal`). It is proved at the level of counts: the
  symmetry of the gap counts gives `N(j) + N(n - j) = N(0)`
  (`firstValueCount_add_firstValueCount_sub`), and `n N(0)/(n + 1)^(n - 1) = 1 + g_n(1)`.
* At the middle point `m = ⌊n/2⌋` (`0`-based), the reflection and the bound on `δ_n` give
  `g_n(m) = -1/(n + 1) + O(m^{-3/2})` (`parkingG_middle`).
-/

public section

namespace Parking

open Finset

/-- The marginal correction `g_n(j) = n μ_n(j) - 1` (`lem:marginal`), where `μ_n` is the
law of the first coordinate of a uniform parking function of size `n`. The `0`-based value
`j : Fin n` stands for the source value `j + 1`. -/
@[expose] noncomputable def parkingG (n : ℕ+) (j : Fin n) : ℝ :=
  (n : ℝ) * (marginal n {j} : ℝ) - 1

/-- `μ_n(j) = (1 + g_n(j)) / n`. -/
theorem marginal_apply_singleton_eq (n : ℕ+) (j : Fin n) :
    (marginal n {j} : ℝ) = (1 + parkingG n j) / n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 n.pos
  rw [eq_div_iff hn.ne', parkingG]
  ring

/-- `1 + g_n(j) = n N(j) / (n + 1)^(n - 1)`, where `N(j) = firstValueCount (n - 1) j` is the
number of parking functions of size `n` with first coordinate `j`. -/
theorem one_add_parkingG (n : ℕ+) (j : Fin n) :
    1 + parkingG n j =
      (n : ℝ) * (firstValueCount ((n : ℕ) - 1) j : ℝ) / ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := by
  rw [parkingG, marginal_apply_singleton, card_firstCoord_eq_firstValueCount,
    card_parkingFunction]
  push_cast
  ring

/-- The Borel weight at a positive integer: `q_{k+1} = e^{-(k+1)} (k + 1)^(k - 1) / k!`.
At `k = 0` both sides equal `e^{-1}`. -/
theorem borelWeight_succ_eq (k : ℕ) :
    borelWeight (k + 1) =
      Real.exp (-((k : ℝ) + 1)) * ((k : ℝ) + 1) ^ (k - 1) / (k.factorial : ℝ) := by
  rcases k with _ | k
  · simp [borelWeight]
  · rw [borelWeight, Nat.factorial_succ (k + 1)]
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    have h1 : ((k : ℝ) + 1 + 1) ≠ 0 := by positivity
    have h2 : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp

/-- The gaps in terms of the gap counts, with `n = a + b + 1` and `i = a`:
`q_{a+1} q_{b+1} / q_{a+b+2} = (a + b + 1) · gapCount (a + b) a / (a + b + 2)^(a + b)`. -/
theorem parkingGap_add_eq_gapCount (a b : ℕ) :
    parkingGap (a + b + 1) a =
      ((a + b + 1 : ℕ) : ℝ) * (gapCount (a + b) a : ℝ) / ((a + b + 2 : ℕ) : ℝ) ^ (a + b) := by
  have hfac : ((a + b + 1).factorial : ℝ) =
      ((a + b + 1 : ℕ) : ℝ) * ((a + b).choose a : ℝ) * (a.factorial : ℝ) *
        (b.factorial : ℝ) := by
    rw [Nat.factorial_succ, ← Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b),
      Nat.add_sub_cancel_left]
    push_cast
    ring
  have hexp : Real.exp (-(((a + b + 1 : ℕ) : ℝ) + 1)) =
      Real.exp (-((a : ℝ) + 1)) * Real.exp (-((b : ℝ) + 1)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [parkingGap, show a + b + 1 - a = b + 1 by omega, borelWeight_succ_eq,
    borelWeight_succ_eq, borelWeight_succ_eq, hexp, hfac, gapCount_eq,
    Nat.add_sub_cancel_left, Nat.add_sub_cancel]
  have e1 : Real.exp (-((a : ℝ) + 1)) ≠ 0 := (Real.exp_pos _).ne'
  have e2 : Real.exp (-((b : ℝ) + 1)) ≠ 0 := (Real.exp_pos _).ne'
  have f1 : (a.factorial : ℝ) ≠ 0 := by positivity
  have f2 : (b.factorial : ℝ) ≠ 0 := by positivity
  have hc : ((a + b).choose a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right a b)).ne'
  push_cast
  have p1 : ((a : ℝ) + b + 1 + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The gaps in terms of the gap counts: for `j < n`,
`δ_n(j) = n · gapCount (n - 1) j / (n + 1)^(n - 1)` (`0`-based `j`). -/
theorem parkingGap_eq_gapCount (n : ℕ+) {j : ℕ} (hj : j < n) :
    parkingGap n j =
      (n : ℝ) * (gapCount ((n : ℕ) - 1) j : ℝ) / ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := by
  obtain ⟨b, hb⟩ : ∃ b, (n : ℕ) = j + b + 1 := ⟨(n : ℕ) - j - 1, by omega⟩
  rw [hb, parkingGap_add_eq_gapCount, Nat.add_sub_cancel]
  push_cast
  ring

/-- `∑_j N(j) = (n + 1)^(n - 1)`: the first-coordinate counts add up to the number of
parking functions of size `n`. -/
theorem sum_firstValueCount_fin (n : ℕ+) :
    ∑ j : Fin n, (firstValueCount ((n : ℕ) - 1) j : ℝ) = ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => (firstValueCount ((n : ℕ) - 1) t : ℝ)) (n : ℕ)]
  obtain ⟨N, hN⟩ : ∃ N, (n : ℕ) = N + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  rw [hN, Nat.add_sub_cancel, ← Nat.cast_sum, sum_firstValueCount]
  push_cast
  ring

/-- `∑_j g_n(j) = 0`, since `μ_n` is a probability law. -/
theorem sum_parkingG (n : ℕ+) : ∑ j, parkingG n j = 0 := by
  have hM : (0 : ℝ) < ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := by positivity
  have h : ∀ j : Fin n, parkingG n j =
      (n : ℝ) / ((n : ℝ) + 1) ^ ((n : ℕ) - 1) * (firstValueCount ((n : ℕ) - 1) j : ℝ) - 1 := by
    intro j
    have := one_add_parkingG n j
    rw [div_mul_eq_mul_div]
    linarith
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_firstValueCount_fin, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, div_mul_cancel₀ _ hM.ne',
    sub_self]

/-- DH17, Corollary 1, for `g_n`: `g_n(j) - g_n(j + 1) = δ_n(j)` (`lem:marginal`,
`0`-based `j`). -/
theorem parkingG_sub_parkingG_succ (n : ℕ+) (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    parkingG n j - parkingG n ⟨j + 1, hj⟩ = parkingGap n j := by
  have h1 := one_add_parkingG n j
  have h2 : 1 + parkingG n ⟨j + 1, hj⟩ = (n : ℝ) *
      (firstValueCount ((n : ℕ) - 1) ((j : ℕ) + 1) : ℝ) / ((n : ℝ) + 1) ^ ((n : ℕ) - 1) :=
    one_add_parkingG n ⟨j + 1, hj⟩
  have h3 : (firstValueCount ((n : ℕ) - 1) j : ℝ) =
      firstValueCount ((n : ℕ) - 1) ((j : ℕ) + 1) + gapCount ((n : ℕ) - 1) j := by
    exact_mod_cast firstValueCount_eq_add (by omega)
  rw [parkingGap_eq_gapCount n j.isLt]
  rw [h3] at h1
  linear_combination h1 - h2

/-- `1 + g_n(j) = ∑_{j ≤ i < n} δ_n(i)` (`0`-based indices). -/
theorem one_add_parkingG_eq_sum (n : ℕ+) (j : Fin n) :
    1 + parkingG n j = ∑ i ∈ Finset.Ico (j : ℕ) n, parkingGap n i := by
  rw [one_add_parkingG, firstValueCount_eq_sum, Nat.sub_add_cancel n.pos, Nat.cast_sum,
    Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [parkingGap_eq_gapCount n (Finset.mem_Ico.1 hi).2]

/-- Telescoping: `g_n(j) = g_n(k) + ∑_{j ≤ i < k} δ_n(i)` for `j ≤ k` (`0`-based). -/
theorem parkingG_eq_add_sum (n : ℕ+) (j k : Fin n) (hjk : j ≤ k) :
    parkingG n j = parkingG n k + ∑ i ∈ Finset.Ico (j : ℕ) k, parkingGap n i := by
  have h1 := one_add_parkingG_eq_sum n j
  have h2 := one_add_parkingG_eq_sum n k
  rw [← Finset.sum_Ico_consecutive _ (show (j : ℕ) ≤ k from hjk) k.isLt.le] at h1
  linarith

/-- `g_n(1) = (n - 1)/(n + 1)` (`lem:marginal`), from `N(0) (n + 1) = 2 (n + 1)^(n - 1)`. -/
theorem parkingG_zero (n : ℕ+) : parkingG n ⟨0, n.pos⟩ = ((n : ℝ) - 1) / ((n : ℝ) + 1) := by
  have h : 1 + parkingG n ⟨0, n.pos⟩ = (n : ℝ) * (firstValueCount ((n : ℕ) - 1) 0 : ℝ) /
      ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := one_add_parkingG n ⟨0, n.pos⟩
  have h0 : (firstValueCount ((n : ℕ) - 1) 0 : ℝ) * ((n : ℝ) + 1) =
      2 * ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := by
    have := firstValueCount_zero_mul ((n : ℕ) - 1)
    rw [show (n : ℕ) - 1 + 2 = (n : ℕ) + 1 by have := n.pos; omega] at this
    exact_mod_cast this
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hM : (0 : ℝ) < ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := by positivity
  have hg : parkingG n ⟨0, n.pos⟩ = (n : ℝ) * (firstValueCount ((n : ℕ) - 1) 0 : ℝ) /
      ((n : ℝ) + 1) ^ ((n : ℕ) - 1) - 1 := by linarith
  rw [hg, div_sub_one hM.ne', div_eq_div_iff hM.ne' hn1.ne']
  linear_combination (n : ℝ) * h0

/-- The last value: `1 + g_n(n) = (n/(n + 1))^(n - 1) = δ_n(1)` for `n ≥ 2` (source
`lem:marginal`). -/
theorem one_add_parkingG_last (n : ℕ+) (hn : 2 ≤ (n : ℕ)) :
    1 + parkingG n ⟨(n : ℕ) - 1, by omega⟩ = ((n : ℝ) / ((n : ℝ) + 1)) ^ ((n : ℕ) - 1) ∧
      ((n : ℝ) / ((n : ℝ) + 1)) ^ ((n : ℕ) - 1) = parkingGap n 0 := by
  refine ⟨?_, ?_⟩
  · rw [one_add_parkingG, firstValueCount_self, Nat.sub_add_cancel (by omega : 1 ≤ (n : ℕ)),
      div_pow]
    push_cast
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ (n : ℕ) - 1)]
  · rw [parkingGap, zero_add, Nat.sub_zero, borelWeight_one_mul_div_succ _ hn]

/-- `g_n` is nonincreasing (`lem:marginal`, `lem:marginal`). -/
theorem parkingG_antitone (n : ℕ+) : Antitone (parkingG n) := by
  intro i j hij
  have hF : (firstValueCount ((n : ℕ) - 1) j : ℝ) ≤ firstValueCount ((n : ℕ) - 1) i := by
    exact_mod_cast antitone_nat_of_succ_le (firstValueCount_succ_le ((n : ℕ) - 1))
      (show (i : ℕ) ≤ j from hij)
  have hi := one_add_parkingG n i
  have hj := one_add_parkingG n j
  have hM : (0 : ℝ) < ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := by positivity
  have : (n : ℝ) * (firstValueCount ((n : ℕ) - 1) j : ℝ) / ((n : ℝ) + 1) ^ ((n : ℕ) - 1) ≤
      (n : ℝ) * (firstValueCount ((n : ℕ) - 1) i : ℝ) / ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := by
    gcongr
  linarith

/-- `e^{-1} ≤ (n/(n + 1))^(n - 1)` for `n ≥ 1`, from `1 + 1/n ≤ e^{1/n}`. -/
theorem exp_neg_one_le_div_pow (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-1) ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ (n - 1) := by
  have hx : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have h1 : (n : ℝ) / ((n : ℝ) + 1) = (1 / (n : ℝ) + 1)⁻¹ := by
    field_simp
    ring
  have h2 : (1 / (n : ℝ) + 1) ^ (n - 1) ≤ Real.exp 1 := by
    calc (1 / (n : ℝ) + 1) ^ (n - 1) ≤ Real.exp (1 / n) ^ (n - 1) :=
          pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = Real.exp (((n - 1 : ℕ) : ℝ) * (1 / n)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 1 := by
          apply Real.exp_le_exp.2
          rw [Nat.cast_sub hn, Nat.cast_one, mul_one_div, div_le_one hx]
          linarith
  rw [h1, inv_pow, Real.exp_neg]
  exact inv_anti₀ (by positivity) h2

/-- `e^{-1} ≤ 1 + g_n(j)` for `n ≥ 2` (`eq:g_bounds`, `lem:marginal`). -/
theorem exp_neg_one_le_one_add_parkingG (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (j : Fin n) :
    Real.exp (-1) ≤ 1 + parkingG n j := by
  have hlast := (one_add_parkingG_last n hn).1
  have hle : parkingG n ⟨(n : ℕ) - 1, by omega⟩ ≤ parkingG n j :=
    parkingG_antitone n (show (j : ℕ) ≤ (n : ℕ) - 1 by have := j.isLt; omega)
  have := exp_neg_one_le_div_pow (n : ℕ) (by omega)
  linarith

/-- `1 + g_n(j) ≤ 2` (`eq:g_bounds`, `lem:marginal`), from `1 + g_n(1) = 2n/(n + 1)`. -/
theorem one_add_parkingG_le_two (n : ℕ+) (j : Fin n) : 1 + parkingG n j ≤ 2 := by
  have hle : parkingG n j ≤ parkingG n ⟨0, n.pos⟩ :=
    parkingG_antitone n (show 0 ≤ (j : ℕ) from Nat.zero_le _)
  have h0 := parkingG_zero n
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : ((n : ℝ) - 1) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn1]
    linarith
  linarith

/-- The reflection of the first-coordinate counts: `N(j) + N(n - j) = N(0)` with `n = N + 1`,
from the symmetry of the gap counts (`0`-based `j`; `N(n) = 0`). -/
theorem firstValueCount_add_firstValueCount_sub (N j : ℕ) (hj : j ≤ N + 1) :
    firstValueCount N j + firstValueCount N (N + 1 - j) = firstValueCount N 0 := by
  induction j with
  | zero => rw [Nat.sub_zero, firstValueCount_eq_zero (Nat.lt_succ_self N), add_zero]
  | succ j ih =>
    have h1 := firstValueCount_eq_add (N := N) (t := j) (by omega)
    have h2 := firstValueCount_eq_add (N := N) (t := N - j) (by omega)
    have h3 := gapCount_symm (N := N) (i := j) (by omega)
    have ih' := ih (by omega)
    rw [show N + 1 - (j + 1) = N - j by omega]
    rw [show N + 1 - j = N - j + 1 by omega] at ih'
    omega

/-- The reflection `g_n(i) + g_n(k) = -2/(n + 1)` whenever `i + k = n` (`0`-based). -/
theorem parkingG_add_parkingG_of_add_eq (n : ℕ+) {i k : ℕ} (hi : i < n) (hk : k < n)
    (hik : i + k = n) :
    parkingG n ⟨i, hi⟩ + parkingG n ⟨k, hk⟩ = -2 / ((n : ℝ) + 1) := by
  have h1 := one_add_parkingG n ⟨i, hi⟩
  have h2 := one_add_parkingG n ⟨k, hk⟩
  have h0 : 1 + parkingG n ⟨0, n.pos⟩ = (n : ℝ) * (firstValueCount ((n : ℕ) - 1) 0 : ℝ) /
      ((n : ℝ) + 1) ^ ((n : ℕ) - 1) := one_add_parkingG n ⟨0, n.pos⟩
  have hc : (firstValueCount ((n : ℕ) - 1) i : ℝ) + firstValueCount ((n : ℕ) - 1) k =
      firstValueCount ((n : ℕ) - 1) 0 := by
    have := firstValueCount_add_firstValueCount_sub ((n : ℕ) - 1) i (by omega)
    rw [show (n : ℕ) - 1 + 1 - i = k by omega] at this
    exact_mod_cast this
  have key : parkingG n ⟨i, hi⟩ + parkingG n ⟨k, hk⟩ = parkingG n ⟨0, n.pos⟩ - 1 := by
    linear_combination h1 + h2 - h0 + ((n : ℝ) / ((n : ℝ) + 1) ^ ((n : ℕ) - 1)) * hc
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [key, parkingG_zero, div_sub_one hn1.ne']
  congr 1
  ring

/-- The reflection `g_n(j) + g_n(n + 2 - j) = -2/(n + 1)` for `2 ≤ j ≤ n`
(`eq:marginal_reflection`, `lem:marginal`); with the `0`-based `j`, the partner of `j` is
`n - j`. -/
theorem parkingG_add_parkingG_reflect (n : ℕ+) (j : Fin n) (hj : 1 ≤ (j : ℕ)) :
    parkingG n j + parkingG n ⟨(n : ℕ) - j, by omega⟩ = -2 / ((n : ℝ) + 1) :=
  parkingG_add_parkingG_of_add_eq n j.isLt _ (by have := j.isLt; omega)

/-- The middle point `m = ⌊n/2⌋` (`0`-based): `-1/(n + 1) ≤ g_n(m) ≤ -1/(n + 1) +
(m + 1)^{-3/2}`. If `n` is even, the reflection gives `g_n(m) = -1/(n + 1)`; if `n` is odd,
it gives `g_n(m) = -1/(n + 1) + δ_n(m)/2` and `0 < δ_n(m) ≤ 2 (m + 1)^{-3/2}`. -/
theorem parkingG_middle (n : ℕ+) (hn : 2 ≤ (n : ℕ)) :
    -1 / ((n : ℝ) + 1) ≤ parkingG n ⟨(n : ℕ) / 2, by omega⟩ ∧
    parkingG n ⟨(n : ℕ) / 2, by omega⟩ ≤ -1 / ((n : ℝ) + 1) +
      1 / ((((n : ℕ) / 2 : ℕ) + 1 : ℝ) * √(((n : ℕ) / 2 : ℕ) + 1 : ℝ)) := by
  have hpos : 0 < 1 / ((((n : ℕ) / 2 : ℕ) + 1 : ℝ) * √(((n : ℕ) / 2 : ℕ) + 1 : ℝ)) := by
    positivity
  have e1 : -2 / ((n : ℝ) + 1) = 2 * (-1 / ((n : ℝ) + 1)) := by ring
  rcases Nat.mod_two_eq_zero_or_one (n : ℕ) with h | h
  · have hr := parkingG_add_parkingG_of_add_eq n (i := (n : ℕ) / 2) (k := (n : ℕ) / 2)
      (by omega) (by omega) (by omega)
    constructor <;> linarith
  · have hr := parkingG_add_parkingG_of_add_eq n (i := (n : ℕ) / 2) (k := (n : ℕ) / 2 + 1)
      (by omega) (by omega) (by omega)
    have hs : parkingG n ⟨(n : ℕ) / 2, by omega⟩ - parkingG n ⟨(n : ℕ) / 2 + 1, by omega⟩ =
        parkingGap n ((n : ℕ) / 2) :=
      parkingG_sub_parkingG_succ n ⟨(n : ℕ) / 2, by omega⟩ (show (n : ℕ) / 2 + 1 < n by omega)
    have hp : 0 < parkingGap n ((n : ℕ) / 2) := parkingGap_pos (by omega)
    have hle := parkingGap_le (n := n) (i := (n : ℕ) / 2) (by omega)
    have e2 : 2 / ((((n : ℕ) / 2 : ℕ) + 1 : ℝ) * √(((n : ℕ) / 2 : ℕ) + 1 : ℝ)) =
        2 * (1 / ((((n : ℕ) / 2 : ℕ) + 1 : ℝ) * √(((n : ℕ) / 2 : ℕ) + 1 : ℝ))) := by ring
    constructor <;> linarith

end Parking

end
