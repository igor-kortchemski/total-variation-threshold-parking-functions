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

public import Parking.SqrtSums
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The split sum in the proof of `lem:products`

This module defines the scale `b_{n,k} = k log(k + 1) / n` of `lem:products` and proves
that, for `1 ≤ k ≤ n`, the split sum

`S(n, k) = (k / n) ∑_{1 ≤ m ≤ n} min (1 / (b_{n,k} m), 1 / √(b_{n,k} m))`

lies in `[1/4, 6]` (`le_sum_min_inv_bScale`, `sum_min_inv_bScale_le`). The sum is written over
`j : Fin n` with `m = j + 1`, as in the other modules of the project.

As in the source (`lem:products`), the sum is split at the integer `a = ⌊n / (k + 1)⌋ + 1`, so
that `1 ≤ a ≤ n` and `n < (k + 1) a ≤ n + k + 1` (`exists_split_point`). Write `L = log (k + 1)`.

* Upper bound. On `m < a`, the summand is at most `1 / √(b m)`, and
  `∑_{1 ≤ m < a} 1 / √m ≤ 2 √a` (`sum_inv_sqrt_le`); the contribution is at most
  `2 √(k a / (n L)) ≤ 2 √(2 / L)`. On `m ≥ a`, the summand is at most `1 / (b m)`, and the
  contribution is at most `(1 + log (n / a)) / L ≤ 1 + 1 / L`. With `L ≥ log 2 > 0.69`, the
  total is less than `3.41 + 2.45 ≤ 6`.
* Lower bound. If `k ≤ 2`, then `b m ≤ k L ≤ k² ≤ 4`, so every summand is at least `1/4` and
  `S ≥ k / 4`. If `k ≥ 3`, then `b m ≥ 1/4` for `m ≥ a`, so the summand is at least
  `1 / (2 b m)`, and `∑_{a ≤ m ≤ n} 1 / m ≥ log ((n + 1) / a) ≥ log ((k + 1) / 2) ≥ L / 2`;
  hence `S ≥ 1/4`.

The harmonic estimates on `[a, n]` (`log_div_le_sum_Icc_inv`, `sum_Icc_inv_le_one_add_log`)
telescope `log (1 + 1/m) ≤ 1/m ≤ -log (1 - 1/m)`.

The module also proves the averaging inequality `mul_sum_range_le_of_antitone`: for an antitone
`f` and `N ≤ n`, the average of `f` over `[0, N)` dominates its average over `[0, n)`.
-/

public section

namespace Parking

open Finset

/-- `b_{n,k} = k log(k+1) / n` (`lem:products`). -/
@[expose] noncomputable def bScale (n k : ℕ) : ℝ := (k : ℝ) * Real.log ((k : ℝ) + 1) / n

/-- `b_{n,k} > 0` for `n ≥ 1` and `k ≥ 1`. -/
theorem bScale_pos {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : 0 < bScale n k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
  exact div_pos (mul_pos (by linarith) hL) hn'

/-! ### Harmonic sums over `[a, n]` -/

/-- The per-term inequality `log (x + 1) - log x ≤ 1 / x`, for `x > 0`. -/
theorem log_add_one_sub_log_le_inv {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) hx.ne', div_sub_one hx.ne'] at h
  have he : (x + 1 - x) / x = 1 / x := by ring
  linarith

/-- The per-term inequality `1 / x ≤ log x - log (x - 1)`, for `x > 1`. -/
theorem inv_le_log_sub_log_sub_one {x : ℝ} (hx : 1 < x) :
    1 / x ≤ Real.log x - Real.log (x - 1) := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (x - 1) / x from div_pos (by linarith) hx0)
  rw [Real.log_div (sub_pos.2 hx).ne' hx0.ne', div_sub_one hx0.ne'] at h
  have he : (x - 1 - x) / x = -(1 / x) := by ring
  linarith

/-- Lower bound of a harmonic sum over an interval: if `1 ≤ a ≤ n + 1`, then
`log ((n + 1) / a) ≤ ∑_{a ≤ m ≤ n} 1 / m`. -/
theorem log_div_le_sum_Icc_inv {a n : ℕ} (ha : 1 ≤ a) (han : a ≤ n + 1) :
    Real.log (((n : ℝ) + 1) / a) ≤ ∑ m ∈ Finset.Icc a n, 1 / (m : ℝ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have htel := sub_le_sum_Ico_of_le (f := fun m : ℕ => 1 / (m : ℝ))
    (g := fun m : ℕ => Real.log (m : ℝ)) han fun m hm _ => by
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hterm := log_add_one_sub_log_le_inv hm0
      push_cast
      exact hterm
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  rw [Real.log_div (by positivity) ha0.ne']
  push_cast at htel
  exact htel

/-- Upper bound of a harmonic sum over an interval: if `1 ≤ a ≤ n`, then
`∑_{a ≤ m ≤ n} 1 / m ≤ 1 + log (n / a)`. -/
theorem sum_Icc_inv_le_one_add_log {a n : ℕ} (ha : 1 ≤ a) (han : a ≤ n) :
    ∑ m ∈ Finset.Icc a n, 1 / (m : ℝ) ≤ 1 + Real.log ((n : ℝ) / a) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have htel := sum_Ico_le_sub_of_le (f := fun m : ℕ => 1 / (m : ℝ))
    (g := fun m : ℕ => Real.log ((m : ℝ) - 1)) (show a + 1 ≤ n + 1 by omega) fun m hm _ => by
      have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
      have hterm := inv_le_log_sub_log_sub_one hm1
      push_cast
      rw [add_sub_cancel_right]
      exact hterm
  push_cast at htel
  simp only [add_sub_cancel_right] at htel
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast ha.trans han
  have h1a : 1 / (a : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact ha1
  rw [Real.log_div (by positivity) (by positivity)]
  linarith

/-! ### Reindexing and pointwise bounds -/

/-- Reindexing a sum over `Fin n` at `j + 1`: `∑_{j < n} f (j + 1) = ∑_{1 ≤ m < n + 1} f m`. -/
theorem sum_fin_eq_sum_Ico_one (n : ℕ) (f : ℝ → ℝ) :
    ∑ j : Fin n, f ((j : ℝ) + 1) = ∑ m ∈ Ico 1 (n + 1), f (m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, sum_Ico_succ_top (by omega : 1 ≤ n + 1), ← ih]
    simp

/-- The split point `a = ⌊n / (k + 1)⌋ + 1`: for `1 ≤ k ≤ n`, there is an integer `a` with
`1 ≤ a ≤ n` and `n < (k + 1) a ≤ n + (k + 1)`. -/
theorem exists_split_point {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ n ∧ n < (k + 1) * a ∧ (k + 1) * a ≤ n + (k + 1) := by
  refine ⟨n / (k + 1) + 1, Nat.le_add_left 1 _, ?_, Nat.lt_mul_div_succ n (by omega), ?_⟩
  · have h₁ : (k + 1) * (n / (k + 1)) ≤ n := Nat.mul_div_le n (k + 1)
    have h₂ : 2 * (n / (k + 1)) ≤ (k + 1) * (n / (k + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have h₁ : (k + 1) * (n / (k + 1)) ≤ n := Nat.mul_div_le n (k + 1)
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- If `0 < x ≤ 4`, then `1 / 4 ≤ min (1 / x) (1 / √x)`. -/
theorem quarter_le_min_inv {x : ℝ} (hx : 0 < x) (hx4 : x ≤ 4) :
    1 / 4 ≤ min (1 / x) (1 / √x) := by
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  have hsx : √x ^ 2 = x := Real.sq_sqrt hx.le
  have hs2 : √x ≤ 2 := by nlinarith
  refine le_min ?_ ?_
  · rw [div_le_div_iff₀ (by norm_num) hx]
    linarith
  · rw [div_le_div_iff₀ (by norm_num) hs]
    linarith

/-- If `1 / 4 ≤ x`, then `1 / (2 x) ≤ min (1 / x) (1 / √x)`. -/
theorem inv_two_mul_le_min_inv {x : ℝ} (hx : 1 / 4 ≤ x) :
    1 / (2 * x) ≤ min (1 / x) (1 / √x) := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := Real.sqrt_pos.2 hx0
  have hsx : √x ^ 2 = x := Real.sq_sqrt hx0.le
  have hs2 : 1 / 2 ≤ √x := by nlinarith
  refine le_min ?_ ?_
  · rw [div_le_div_iff₀ (by positivity) hx0]
    linarith
  · rw [div_le_div_iff₀ (by positivity) hs]
    nlinarith

/-! ### The split sum -/

/-- Upper bound of the split sum of `lem:products`: for `1 ≤ k ≤ n`,
`(k / n) ∑_{j < n} min (1 / (b_{n,k} (j + 1)), 1 / √(b_{n,k} (j + 1))) ≤ 6`. -/
theorem sum_min_inv_bScale_le (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (k : ℝ) / n * ∑ j : Fin n, min (1 / (bScale n k * ((j : ℝ) + 1)))
      (1 / √(bScale n k * ((j : ℝ) + 1))) ≤ 6 := by
  have hn : 1 ≤ n := hk.trans hkn
  have hb : 0 < bScale n k := bScale_pos hn hk
  rw [sum_fin_eq_sum_Ico_one n fun x => min (1 / (bScale n k * x)) (1 / √(bScale n k * x))]
  have hbL : bScale n k = k * Real.log ((k : ℝ) + 1) / n := rfl
  generalize bScale n k = b at hb hbL ⊢
  set L := Real.log ((k : ℝ) + 1) with hL_def
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hL2 : 0.69 < L := by
    have h₁ := Real.log_two_gt_d9
    have h₂ : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨a, ha1, han, hlt, hle⟩ := exists_split_point hk hkn
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hlt' : (n : ℝ) < (k + 1) * a := by exact_mod_cast hlt
  have hle' : ((k : ℝ) + 1) * a ≤ n + (k + 1) := by exact_mod_cast hle
  rw [← sum_Ico_consecutive _ ha1 (show a ≤ n + 1 by omega)]
  -- The lower part, `m < a`.
  have hlow : ∑ m ∈ Ico 1 a, min (1 / (b * m)) (1 / √(b * m)) ≤ 2 * √(a : ℝ) / √b := by
    calc ∑ m ∈ Ico 1 a, min (1 / (b * m)) (1 / √(b * m))
        ≤ ∑ m ∈ Ico 1 a, 1 / √b * (1 / √(m : ℝ)) := by
          refine sum_le_sum fun m _ => ?_
          rw [Real.sqrt_mul hb.le, one_div_mul_one_div]
          exact min_le_right _ _
      _ = 1 / √b * ∑ m ∈ Ico 1 a, 1 / √(m : ℝ) := by rw [mul_sum]
      _ ≤ 1 / √b * (2 * √(a : ℝ)) := by gcongr; exact sum_inv_sqrt_le a
      _ = 2 * √(a : ℝ) / √b := by ring
  -- The upper part, `a ≤ m ≤ n`.
  have hlogn : Real.log ((n : ℝ) / a) ≤ L := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ ha0]
    linarith
  have hup : ∑ m ∈ Ico a (n + 1), min (1 / (b * m)) (1 / √(b * m)) ≤ 1 / b * (1 + L) := by
    calc ∑ m ∈ Ico a (n + 1), min (1 / (b * m)) (1 / √(b * m))
        ≤ ∑ m ∈ Ico a (n + 1), 1 / b * (1 / (m : ℝ)) := by
          refine sum_le_sum fun m _ => ?_
          rw [one_div_mul_one_div]
          exact min_le_left _ _
      _ = 1 / b * ∑ m ∈ Icc a n, 1 / (m : ℝ) := by rw [mul_sum, Ico_add_one_right_eq_Icc]
      _ ≤ 1 / b * (1 + L) := by
          gcongr
          linarith [sum_Icc_inv_le_one_add_log ha1 han]
  -- The two contributions.
  set X := (k : ℝ) / n * (2 * √(a : ℝ) / √b) with hX_def
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ^ 2 = 4 * ((k : ℝ) * a / n) / L := by
    have hsa := Real.sq_sqrt ha0.le
    have hsb := Real.sq_sqrt hb.le
    have hsb0 : 0 < √b := Real.sqrt_pos.2 hb
    calc X ^ 2 = ((k : ℝ) / n) ^ 2 * 4 * √(a : ℝ) ^ 2 / √b ^ 2 := by rw [hX_def]; ring
      _ = 4 * ((k : ℝ) * a / n) / L := by
        rw [hsa, hsb, hbL]
        field_simp
  have hka : (k : ℝ) * a / n ≤ 2 := by
    rw [div_le_iff₀ hn0]
    nlinarith
  have hX2le : X ^ 2 ≤ 8 / 0.69 := by
    rw [hX2]
    calc 4 * ((k : ℝ) * a / n) / L ≤ 4 * 2 / L := by gcongr
      _ ≤ 8 / 0.69 := by
        rw [div_le_div_iff₀ hL0 (by norm_num)]
        linarith
  have hX : X ≤ 3.41 := by nlinarith
  have hupper : (k : ℝ) / n * (1 / b * (1 + L)) = 1 + 1 / L := by
    rw [hbL]
    field_simp
    ring
  have hinvL : 1 / L ≤ 1 / 0.69 := one_div_le_one_div_of_le (by norm_num) hL2.le
  have hkn0 : 0 ≤ (k : ℝ) / n := by positivity
  calc (k : ℝ) / n * (∑ m ∈ Ico 1 a, min (1 / (b * m)) (1 / √(b * m)) +
        ∑ m ∈ Ico a (n + 1), min (1 / (b * m)) (1 / √(b * m)))
      ≤ (k : ℝ) / n * (2 * √(a : ℝ) / √b + 1 / b * (1 + L)) := by gcongr
    _ = X + (k : ℝ) / n * (1 / b * (1 + L)) := by rw [hX_def]; ring
    _ ≤ 6 := by
      rw [hupper]
      norm_num at hinvL ⊢
      linarith

/-- Lower bound of the split sum of `lem:products`: for `1 ≤ k ≤ n`,
`1 / 4 ≤ (k / n) ∑_{j < n} min (1 / (b_{n,k} (j + 1)), 1 / √(b_{n,k} (j + 1)))`. -/
theorem le_sum_min_inv_bScale (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    1 / 4 ≤ (k : ℝ) / n * ∑ j : Fin n, min (1 / (bScale n k * ((j : ℝ) + 1)))
      (1 / √(bScale n k * ((j : ℝ) + 1))) := by
  have hn : 1 ≤ n := hk.trans hkn
  have hb : 0 < bScale n k := bScale_pos hn hk
  rw [sum_fin_eq_sum_Ico_one n fun x => min (1 / (bScale n k * x)) (1 / √(bScale n k * x))]
  have hbL : bScale n k = k * Real.log ((k : ℝ) + 1) / n := rfl
  generalize bScale n k = b at hb hbL ⊢
  set L := Real.log ((k : ℝ) + 1) with hL_def
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL2 : 1 / 2 < Real.log 2 := by
    have h₁ := Real.log_two_gt_d9
    norm_num at h₁ ⊢
    linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hbn : b * n = k * L := by
    rw [hbL]
    field_simp
  have hnonneg : ∀ m ∈ Ico 1 (n + 1), 0 ≤ min (1 / (b * m)) (1 / √(b * (m : ℝ))) :=
    fun m _ => le_min (by positivity) (by positivity)
  rcases le_or_gt k 2 with hk2 | hk3
  · -- If `k ≤ 2`, every summand is at least `1/4`.
    have hk2' : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    have hLk : L ≤ k := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (k : ℝ) + 1 by positivity)
      linarith
    have hterm : ∀ m ∈ Ico 1 (n + 1), (1 : ℝ) / 4 ≤ min (1 / (b * m)) (1 / √(b * (m : ℝ))) := by
      intro m hm
      rw [mem_Ico] at hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
      have hmn : (m : ℝ) ≤ n := by exact_mod_cast (show m ≤ n by omega)
      refine quarter_le_min_inv (by positivity) ?_
      calc b * m ≤ b * n := by gcongr
        _ = k * L := hbn
        _ ≤ 2 * 2 := by gcongr; linarith
        _ = 4 := by norm_num
    have hcard := card_nsmul_le_sum (Ico 1 (n + 1))
      (fun m : ℕ => min (1 / (b * m)) (1 / √(b * (m : ℝ)))) (1 / 4) hterm
    rw [Nat.card_Ico, add_tsub_cancel_right, nsmul_eq_mul] at hcard
    have hval : (k : ℝ) / n * (n * (1 / 4)) = k / 4 := by field_simp
    calc (1 : ℝ) / 4 ≤ (k : ℝ) / n * (n * (1 / 4)) := by rw [hval]; linarith
      _ ≤ _ := by gcongr
  · -- If `k ≥ 3`, the summands with `m ≥ a` are at least `1 / (2 b m)`.
    have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    obtain ⟨a, ha1, han, hlt, hle⟩ := exists_split_point hk hkn
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have hlt' : (n : ℝ) < (k + 1) * a := by exact_mod_cast hlt
    have hle' : ((k : ℝ) + 1) * a ≤ n + (k + 1) := by exact_mod_cast hle
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hLge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have hba : 1 / 4 ≤ b * a := by
      rw [hbL, div_mul_eq_mul_div, le_div_iff₀ hn0]
      nlinarith [mul_nonneg (mul_nonneg ha0.le (by linarith : (0 : ℝ) ≤ k))
        (sub_nonneg.2 (hL2.le.trans hLge)), mul_nonneg ha0.le (sub_nonneg.2 hk1)]
    have hterm : ∀ m ∈ Ico a (n + 1),
        1 / (2 * b) * (1 / (m : ℝ)) ≤ min (1 / (b * m)) (1 / √(b * (m : ℝ))) := by
      intro m hm
      rw [mem_Ico] at hm
      have hma : (a : ℝ) ≤ m := by exact_mod_cast hm.1
      have hbm : 1 / 4 ≤ b * m := hba.trans (by gcongr)
      calc 1 / (2 * b) * (1 / (m : ℝ)) = 1 / (2 * (b * m)) := by
            rw [one_div_mul_one_div, mul_assoc]
        _ ≤ _ := inv_two_mul_le_min_inv hbm
    have hlog : L / 2 ≤ ∑ m ∈ Icc a n, 1 / (m : ℝ) := by
      refine le_trans ?_ (log_div_le_sum_Icc_inv ha1 (by omega))
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have hL4 : Real.log 4 ≤ L := Real.log_le_log (by norm_num) (by linarith)
      have hdiv : ((k : ℝ) + 1) / 2 ≤ ((n : ℝ) + 1) / a := by
        rw [div_le_div_iff₀ (by norm_num) ha0]
        linarith
      have hlog2 : Real.log (((k : ℝ) + 1) / 2) = L - Real.log 2 :=
        Real.log_div (by positivity) (by norm_num)
      have hmono := Real.log_le_log (by positivity) hdiv
      linarith
    have hval : (k : ℝ) / n * (1 / (2 * b) * (L / 2)) = 1 / 4 := by
      rw [hbL]
      field_simp
      ring
    calc (1 : ℝ) / 4 = (k : ℝ) / n * (1 / (2 * b) * (L / 2)) := hval.symm
      _ ≤ (k : ℝ) / n * (1 / (2 * b) * ∑ m ∈ Icc a n, 1 / (m : ℝ)) := by gcongr
      _ = (k : ℝ) / n * ∑ m ∈ Ico a (n + 1), 1 / (2 * b) * (1 / (m : ℝ)) := by
        rw [mul_sum, Ico_add_one_right_eq_Icc]
      _ ≤ (k : ℝ) / n * ∑ m ∈ Ico a (n + 1), min (1 / (b * m)) (1 / √(b * (m : ℝ))) := by
        gcongr with m hm
        exact hterm m hm
      _ ≤ (k : ℝ) / n * ∑ m ∈ Ico 1 (n + 1), min (1 / (b * m)) (1 / √(b * (m : ℝ))) := by
        exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_left ha1)
          fun m hm _ => hnonneg m hm) (by positivity)

/-! ### Averages of antitone sequences -/

/-- For an antitone `f : ℕ → ℝ` and `N ≤ n`, the average of `f` over `[0, N)` dominates its
average over `[0, n)`: `N ∑_{m < n} f m ≤ n ∑_{m < N} f m`. No sign condition is needed. -/
theorem mul_sum_range_le_of_antitone {f : ℕ → ℝ} (hf : Antitone f) {N n : ℕ} (hNn : N ≤ n) :
    (N : ℝ) * ∑ m ∈ Finset.range n, f m ≤ n * ∑ m ∈ Finset.range N, f m := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [← sum_range_add_sum_Ico f hNn]
    have h₁ := sum_le_card_nsmul (Ico N n) f (f (N - 1)) fun m hm => hf (by
      rw [mem_Ico] at hm
      omega)
    have h₂ := card_nsmul_le_sum (range N) f (f (N - 1)) fun m hm => hf (by
      rw [mem_range] at hm
      omega)
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hNn] at h₁
    rw [card_range, nsmul_eq_mul] at h₂
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hnN : (0 : ℝ) ≤ n - N := sub_nonneg.2 (by exact_mod_cast hNn)
    have h₃ := mul_le_mul_of_nonneg_left h₁ hN0
    have h₄ := mul_le_mul_of_nonneg_left h₂ hnN
    linarith

end Parking
