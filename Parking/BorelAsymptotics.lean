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

public import Parking.Borel
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Robbins' bound and the gaps of the marginal correction

This module proves the Stirling estimates used in the
proof of `lem:marginal`, stated for the gaps

`parkingGap n i = q_{i+1} q_{n-i} / q_{n+1}`,

where `q_k = borelWeight k = e^{-k} k^{k-1} / k!`. With the `1`-based index of the source,
`parkingGap n i` is `δ_n(i + 1) = g_n(i + 1) - g_n(i + 2)` (`lem:marginal`).

* Robbins' upper bound `s_m ≤ √π e^{1/(12 m)}` for the Stirling sequence
  `s_m = m! / (√(2m) (m/e)^m)` (`stirlingSeq_le_sqrt_pi_mul_exp`), obtained by telescoping
  Mathlib's stepwise bound `Stirling.log_stirlingSeq_sdiff_le` and passing to the limit
  `s_m → √π`; together with Mathlib's lower bound `√π ≤ s_m`, it gives the weak form of
  [Rob55] used by the source (`exists_factorial_eq_robbins`).
* `q_k = (√π / s_k) · (2π)^{-1/2} k^{-3/2}` (`borelWeight_eq_stirlingSeq`), hence
  `(1 - 1/(12k)) (2π)^{-1/2} k^{-3/2} ≤ q_k ≤ (2π)^{-1/2} k^{-3/2}`.
* For `b ≤ N ≤ 2b`, `1 - 1/(12b) ≤ q_b / q_N ≤ 2N/b - 1` (`le_borelWeight_div`,
  `borelWeight_div_le`), from `s_N ≤ s_b` and `(N/b)^{3/2} ≤ 2N/b - 1`.
* Consequently, for `2(i+1) ≤ n+1`, the gap `parkingGap n i` is comparable to
  `(i+1)^{-3/2}` (`parkingGap_le`, `le_parkingGap`) and equals
  `(2π)^{-1/2} (i+1)^{-3/2}` up to `(2π)^{-1/2} (i+1)^{-1/2} (1/(12 (i+1)^2) + 4/(n+1))`
  (`abs_parkingGap_sub_le`). The gaps are positive and symmetric (`parkingGap_pos`,
  `parkingGap_symm`).
-/

public section

namespace Parking

open Filter Topology

/-- The gap `δ_n(i + 1) = q_{i+1} q_{n-i} / q_{n+1}` between consecutive values of the
marginal correction `g_n` (`lem:marginal`), with `0`-based index `i`. -/
@[expose] noncomputable def parkingGap (n i : ℕ) : ℝ :=
  borelWeight (i + 1) * borelWeight (n - i) / borelWeight (n + 1)

/-! ### Robbins' bound -/

/-- Every Borel weight is positive; at `i = 0` the formula gives `1`. -/
theorem borelWeight_pos (i : ℕ) : 0 < borelWeight i := by
  rcases i with _ | i
  · simp [borelWeight]
  · unfold borelWeight
    positivity

/-- The Stirling sequence is positive at every positive integer. -/
theorem stirlingSeq_pos {m : ℕ} (hm : m ≠ 0) : 0 < Stirling.stirlingSeq m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact Stirling.stirlingSeq'_pos k

/-- The Stirling sequence is nonincreasing on the positive integers. -/
theorem stirlingSeq_le_stirlingSeq {m M : ℕ} (hm : m ≠ 0) (h : m ≤ M) :
    Stirling.stirlingSeq M ≤ Stirling.stirlingSeq m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  exact Stirling.stirlingSeq'_antitone (by omega : k ≤ K)

/-- The Stirling sequence is at most its first value `s_1 = e / √2`. -/
theorem stirlingSeq_le_exp_one_div_sqrt_two {m : ℕ} (hm : m ≠ 0) :
    Stirling.stirlingSeq m ≤ Real.exp 1 / √2 := by
  rw [← Stirling.stirlingSeq_one]
  exact stirlingSeq_le_stirlingSeq one_ne_zero (by omega)

/-- Robbins' upper bound `s_m ≤ √π e^{1/(12m)}` for the Stirling sequence
`s_m = m! / (√(2m) (m/e)^m)`. The sequence `log s_k - 1/(12k)` is nondecreasing by
`Stirling.log_stirlingSeq_sdiff_le`, and `s_k → √π`. -/
theorem stirlingSeq_le_sqrt_pi_mul_exp {m : ℕ} (hm : m ≠ 0) :
    Stirling.stirlingSeq m ≤ √Real.pi * Real.exp (1 / (12 * m)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hmono : Monotone fun j : ℕ =>
      Real.log (Stirling.stirlingSeq (j + 1)) - 1 / (12 * ((j : ℝ) + 1)) := by
    refine monotone_nat_of_le_succ fun j => ?_
    have h := Stirling.log_stirlingSeq_sdiff_le (j + 1)
    have e : (1 : ℝ) / (12 * ((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1)) =
        1 / (12 * ((j : ℝ) + 1)) - 1 / (12 * (((j + 1 : ℕ) : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    rw [e] at h
    push_cast at h ⊢
    linarith
  have hlow : ∀ M : ℕ, k ≤ M → Stirling.stirlingSeq (k + 1) *
      Real.exp (-(1 / (12 * ((k : ℝ) + 1)))) ≤ Stirling.stirlingSeq (M + 1) := by
    intro M hM
    have h1 := hmono hM
    simp only at h1
    have hk := Stirling.stirlingSeq'_pos k
    have hM' := Stirling.stirlingSeq'_pos M
    have h2 : 0 ≤ 1 / (12 * ((M : ℝ) + 1)) := by positivity
    calc Stirling.stirlingSeq (k + 1) * Real.exp (-(1 / (12 * ((k : ℝ) + 1))))
        = Real.exp (Real.log (Stirling.stirlingSeq (k + 1)) - 1 / (12 * ((k : ℝ) + 1))) := by
          rw [Real.exp_sub, Real.exp_log hk, Real.exp_neg]
          ring
      _ ≤ Real.exp (Real.log (Stirling.stirlingSeq (M + 1))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Stirling.stirlingSeq (M + 1) := Real.exp_log hM'
  have hlim : Tendsto (fun M : ℕ => Stirling.stirlingSeq (M + 1)) atTop (𝓝 (√Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
  have hle := ge_of_tendsto hlim (eventually_atTop.2 ⟨k, hlow⟩)
  push_cast
  calc Stirling.stirlingSeq (k + 1)
      = Stirling.stirlingSeq (k + 1) * Real.exp (-(1 / (12 * ((k : ℝ) + 1)))) *
          Real.exp (1 / (12 * ((k : ℝ) + 1))) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ √Real.pi * Real.exp (1 / (12 * ((k : ℝ) + 1))) := by gcongr

/-- Robbins' form of Stirling's formula, weak version [Rob55]:
`m! = √(2πm) (m/e)^m e^r` with `0 ≤ r ≤ 1/(12m)`. -/
theorem exists_factorial_eq_robbins {m : ℕ} (hm : m ≠ 0) : ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 / (12 * m) ∧
    (m.factorial : ℝ) = √(2 * Real.pi * m) * ((m : ℝ) / Real.exp 1) ^ m * Real.exp r := by
  have hs := stirlingSeq_pos hm
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  refine ⟨Real.log (Stirling.stirlingSeq m / √Real.pi), ?_, ?_, ?_⟩
  · apply Real.log_nonneg
    rw [le_div_iff₀ hpi, one_mul]
    exact Stirling.sqrt_pi_le_stirlingSeq hm
  · rw [Real.log_le_iff_le_exp (div_pos hs hpi), div_le_iff₀ hpi, mul_comm]
    exact stirlingSeq_le_sqrt_pi_mul_exp hm
  · rw [Real.exp_log (div_pos hs hpi)]
    have hm' : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
    have hsq : √(2 * Real.pi * m) = √Real.pi * √(2 * m) := by
      rw [← Real.sqrt_mul Real.pi_pos.le]
      congr 1
      ring
    rw [hsq]
    unfold Stirling.stirlingSeq
    have h2 : √(2 * (m : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    have h3 : ((m : ℝ) / Real.exp 1) ^ m ≠ 0 := by positivity
    have h4 : √Real.pi ≠ 0 := hpi.ne'
    field_simp

/-! ### Borel weights -/

/-- The Borel weight in terms of the Stirling sequence:
`q_k = (√π / s_k) · 1 / (√(2π) k √k)` for `k ≥ 1`. -/
theorem borelWeight_eq_stirlingSeq {k : ℕ} (hk : k ≠ 0) :
    borelWeight k =
      √Real.pi / Stirling.stirlingSeq k * (1 / (√(2 * Real.pi) * k * √k)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold borelWeight Stirling.stirlingSeq
  rw [Nat.add_sub_cancel, div_pow, Real.exp_one_pow, Real.exp_neg]
  push_cast
  have hK : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h2pi : √(2 * Real.pi) = √2 * √Real.pi := Real.sqrt_mul (by norm_num) _
  have h2K : √(2 * ((j : ℝ) + 1)) = √2 * √((j : ℝ) + 1) := Real.sqrt_mul (by norm_num) _
  rw [h2pi, h2K, pow_succ]
  have h1 : √((j : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hK).ne'
  have h2 : √(2 : ℝ) ≠ 0 := by positivity
  have h3 : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have h4 : Real.exp ((j : ℝ) + 1) ≠ 0 := (Real.exp_pos _).ne'
  have h5 : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  have h6 : (j : ℝ) + 1 ≠ 0 := hK.ne'
  field_simp

/-- The ratio `√π / s_k` is at least `1 - 1/(12k)`, by Robbins' bound. -/
theorem one_sub_le_sqrt_pi_div_stirlingSeq {k : ℕ} (hk : k ≠ 0) :
    1 - 1 / (12 * (k : ℝ)) ≤ √Real.pi / Stirling.stirlingSeq k := by
  have hs := stirlingSeq_pos hk
  have hk' : (1 : ℝ) ≤ k := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hk)
  have hc1 : 1 / (12 * (k : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  rw [le_div_iff₀ hs]
  have h1 : 1 - 1 / (12 * (k : ℝ)) ≤ Real.exp (-(1 / (12 * (k : ℝ)))) := by
    linarith [Real.add_one_le_exp (-(1 / (12 * (k : ℝ))))]
  have h2 := stirlingSeq_le_sqrt_pi_mul_exp hk
  calc (1 - 1 / (12 * (k : ℝ))) * Stirling.stirlingSeq k
      ≤ (1 - 1 / (12 * (k : ℝ))) * (√Real.pi * Real.exp (1 / (12 * (k : ℝ)))) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = √Real.pi * ((1 - 1 / (12 * (k : ℝ))) * Real.exp (1 / (12 * (k : ℝ)))) := by ring
    _ ≤ √Real.pi * (Real.exp (-(1 / (12 * (k : ℝ)))) * Real.exp (1 / (12 * (k : ℝ)))) := by
        gcongr
    _ = √Real.pi := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- Upper bound `q_k ≤ (2π)^{-1/2} k^{-3/2}` for `k ≥ 1`. -/
theorem borelWeight_le {k : ℕ} (hk : k ≠ 0) :
    borelWeight k ≤ 1 / (√(2 * Real.pi) * k * √k) := by
  rw [borelWeight_eq_stirlingSeq hk]
  have hs := stirlingSeq_pos hk
  have hA : √Real.pi / Stirling.stirlingSeq k ≤ 1 := by
    rw [div_le_one hs]
    exact Stirling.sqrt_pi_le_stirlingSeq hk
  have hp : 0 ≤ 1 / (√(2 * Real.pi) * k * √k) := by positivity
  calc _ ≤ 1 * (1 / (√(2 * Real.pi) * k * √k)) := mul_le_mul_of_nonneg_right hA hp
    _ = _ := one_mul _

/-- Lower bound `(1 - 1/(12k)) (2π)^{-1/2} k^{-3/2} ≤ q_k` for `k ≥ 1`. -/
theorem le_borelWeight {k : ℕ} (hk : k ≠ 0) :
    (1 - 1 / (12 * (k : ℝ))) * (1 / (√(2 * Real.pi) * k * √k)) ≤ borelWeight k := by
  rw [borelWeight_eq_stirlingSeq hk]
  have hp : 0 ≤ 1 / (√(2 * Real.pi) * k * √k) := by positivity
  exact mul_le_mul_of_nonneg_right (one_sub_le_sqrt_pi_div_stirlingSeq hk) hp

/-- The deficit `(2π)^{-1/2} k^{-3/2} - q_k` is at most `(2π)^{-1/2} k^{-5/2} / 12`. -/
theorem sub_borelWeight_le {k : ℕ} (hk : k ≠ 0) :
    1 / (√(2 * Real.pi) * k * √k) - borelWeight k ≤
      1 / (12 * √(2 * Real.pi) * (k : ℝ) ^ 2 * √k) := by
  have h := le_borelWeight hk
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have h1 : √(2 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have h2 : √(k : ℝ) ≠ 0 := (Real.sqrt_pos.2 hk').ne'
  have h3 : (k : ℝ) ≠ 0 := hk'.ne'
  have e : 1 / (12 * √(2 * Real.pi) * (k : ℝ) ^ 2 * √k) =
      1 / (12 * (k : ℝ)) * (1 / (√(2 * Real.pi) * k * √k)) := by
    field_simp
  rw [e]
  linarith

/-- The ratio `q_b / q_N` in terms of the Stirling sequence:
`q_b / q_N = (s_N / s_b) · N √N / (b √b)` for `b, N ≥ 1`. -/
theorem borelWeight_div_borelWeight_eq {b N : ℕ} (hb : b ≠ 0) (hN : N ≠ 0) :
    borelWeight b / borelWeight N =
      Stirling.stirlingSeq N / Stirling.stirlingSeq b * ((N : ℝ) * √N / ((b : ℝ) * √b)) := by
  rw [borelWeight_eq_stirlingSeq hb, borelWeight_eq_stirlingSeq hN]
  have h1 := (stirlingSeq_pos hb).ne'
  have h2 := (stirlingSeq_pos hN).ne'
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 (Nat.pos_of_ne_zero hb)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have h3 : √(b : ℝ) ≠ 0 := (Real.sqrt_pos.2 hb').ne'
  have h4 : √(N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN').ne'
  have h5 : √(2 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have h6 : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have h7 : (b : ℝ) ≠ 0 := hb'.ne'
  have h8 : (N : ℝ) ≠ 0 := hN'.ne'
  field_simp

/-- Upper bound `q_b / q_N ≤ 2N/b - 1` for `1 ≤ b ≤ N ≤ 2b`: `s_N ≤ s_b`, and
`(N/b)^{3/2} ≤ 2N/b - 1` since `N/b ∈ [1, 2]`. -/
theorem borelWeight_div_le {b N : ℕ} (hb : b ≠ 0) (hbN : b ≤ N) (hN : N ≤ 2 * b) :
    borelWeight b / borelWeight N ≤ 2 * (N : ℝ) / b - 1 := by
  have hN0 : N ≠ 0 := by omega
  rw [borelWeight_div_borelWeight_eq hb hN0]
  have hsb := stirlingSeq_pos hb
  have hB : Stirling.stirlingSeq N / Stirling.stirlingSeq b ≤ 1 :=
    (div_le_one hsb).2 (stirlingSeq_le_stirlingSeq hb hbN)
  have hbpos : (0 : ℝ) < b := Nat.cast_pos.2 (Nat.pos_of_ne_zero hb)
  have hbN' : (b : ℝ) ≤ N := Nat.cast_le.2 hbN
  have hN' : (N : ℝ) ≤ 2 * b := by exact_mod_cast hN
  have hy0 : 0 < √(b : ℝ) := Real.sqrt_pos.2 hbpos
  have hxy : √(b : ℝ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt hbN'
  have hx2 : √(N : ℝ) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hy2 : √(b : ℝ) ^ 2 = b := Real.sq_sqrt hbpos.le
  have hD : (N : ℝ) * √N / ((b : ℝ) * √b) ≤ 2 * (N : ℝ) / b - 1 := by
    rw [div_le_iff₀ (by positivity)]
    have e : (2 * (N : ℝ) / b - 1) * ((b : ℝ) * √b) = (2 * (N : ℝ) - b) * √b := by
      field_simp
    rw [e]
    set x := √(N : ℝ)
    set y := √(b : ℝ)
    rw [← hx2, ← hy2]
    have h2 : 0 ≤ 2 * y ^ 2 - x ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hxy) h2, mul_nonneg hy0.le (sq_nonneg (x - y))]
  have hD0 : 0 ≤ (N : ℝ) * √N / ((b : ℝ) * √b) := by positivity
  calc _ ≤ 1 * ((N : ℝ) * √N / ((b : ℝ) * √b)) := mul_le_mul_of_nonneg_right hB hD0
    _ ≤ _ := by rw [one_mul]; exact hD

/-- Lower bound `1 - 1/(12b) ≤ q_b / q_N` for `1 ≤ b ≤ N`: `√π ≤ s_N`, Robbins' bound for
`s_b`, and `N √N ≥ b √b`. -/
theorem le_borelWeight_div {b N : ℕ} (hb : b ≠ 0) (hbN : b ≤ N) :
    1 - 1 / (12 * (b : ℝ)) ≤ borelWeight b / borelWeight N := by
  have hN0 : N ≠ 0 := by omega
  rw [borelWeight_div_borelWeight_eq hb hN0]
  have hsb := stirlingSeq_pos hb
  have hsN := stirlingSeq_pos hN0
  have hB : 1 - 1 / (12 * (b : ℝ)) ≤ Stirling.stirlingSeq N / Stirling.stirlingSeq b :=
    (one_sub_le_sqrt_pi_div_stirlingSeq hb).trans
      (div_le_div_of_nonneg_right (Stirling.sqrt_pi_le_stirlingSeq hN0) hsb.le)
  have hbpos : (0 : ℝ) < b := Nat.cast_pos.2 (Nat.pos_of_ne_zero hb)
  have hbN' : (b : ℝ) ≤ N := Nat.cast_le.2 hbN
  have hD : 1 ≤ (N : ℝ) * √N / ((b : ℝ) * √b) := by
    rw [one_le_div (by positivity)]
    exact mul_le_mul hbN' (Real.sqrt_le_sqrt hbN') (Real.sqrt_nonneg _) (by positivity)
  have hB0 : 0 ≤ Stirling.stirlingSeq N / Stirling.stirlingSeq b := (div_pos hsN hsb).le
  calc _ ≤ Stirling.stirlingSeq N / Stirling.stirlingSeq b * 1 := by rw [mul_one]; exact hB
    _ ≤ _ := mul_le_mul_of_nonneg_left hD hB0

/-! ### The gaps -/

/-- The gaps are positive. Positivity holds for all `n` and `i`; the range `i < n` of the
source is kept in the statement. -/
theorem parkingGap_pos {n i : ℕ} (hi : i < n) : 0 < parkingGap n i := by
  have _ : i < n := hi
  exact div_pos (mul_pos (borelWeight_pos _) (borelWeight_pos _)) (borelWeight_pos _)

/-- The gaps are symmetric: `δ_n(i) = δ_n(n + 1 - i)` in the `1`-based indexing of the
`lem:marginal`. -/
theorem parkingGap_symm {n i : ℕ} (hi : i < n) : parkingGap n (n - 1 - i) = parkingGap n i := by
  unfold parkingGap
  rw [show n - 1 - i + 1 = n - i by omega, show n - (n - 1 - i) = i + 1 by omega, mul_comm]

/-- The bounds on the factors of `parkingGap n i = q_{i+1} · (q_{n-i} / q_{n+1})` used in
the three estimates below, for `2(i+1) ≤ n+1`, with `b = n - i ≥ i + 1`. -/
theorem parkingGap_factor_bounds {n i : ℕ} (h : 2 * (i + 1) ≤ n + 1) :
    parkingGap n i = borelWeight (i + 1) * (borelWeight (n - i) / borelWeight (n + 1)) ∧
    0 < borelWeight (i + 1) ∧
    borelWeight (i + 1) ≤ 1 / (√(2 * Real.pi) * ((i : ℝ) + 1) * √((i : ℝ) + 1)) ∧
    1 / (√(2 * Real.pi) * ((i : ℝ) + 1) * √((i : ℝ) + 1)) - borelWeight (i + 1) ≤
      1 / (12 * √(2 * Real.pi) * ((i : ℝ) + 1) ^ 2 * √((i : ℝ) + 1)) ∧
    (1 - 1 / (12 * ((i : ℝ) + 1))) * (1 / (√(2 * Real.pi) * ((i : ℝ) + 1) * √((i : ℝ) + 1))) ≤
      borelWeight (i + 1) ∧
    1 - 1 / (12 * ((n - i : ℕ) : ℝ)) ≤ borelWeight (n - i) / borelWeight (n + 1) ∧
    borelWeight (n - i) / borelWeight (n + 1) ≤ 2 * ((n : ℝ) + 1) / ((n - i : ℕ) : ℝ) - 1 ∧
    ((n - i : ℕ) : ℝ) + ((i : ℝ) + 1) = (n : ℝ) + 1 ∧
    (i : ℝ) + 1 ≤ ((n - i : ℕ) : ℝ) ∧
    1 ≤ (i : ℝ) + 1 := by
  have hb : n - i ≠ 0 := by omega
  have hq := borelWeight_le (k := i + 1) (by omega)
  have hpq := sub_borelWeight_le (k := i + 1) (by omega)
  have hq' := le_borelWeight (k := i + 1) (by omega)
  have hR1 := le_borelWeight_div hb (by omega : n - i ≤ n + 1)
  have hR2 := borelWeight_div_le hb (by omega : n - i ≤ n + 1) (by omega : n + 1 ≤ 2 * (n - i))
  push_cast at hq hpq hq' hR2
  have hsum : (n - i) + (i + 1) = n + 1 := by omega
  have hab : i + 1 ≤ n - i := by omega
  refine ⟨mul_div_assoc _ _ _, borelWeight_pos _, hq, hpq, hq', hR1, hR2, ?_, ?_, ?_⟩
  · exact_mod_cast hsum
  · exact_mod_cast hab
  · linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]

/-- Upper bound `δ_n(i + 1) ≤ 2 (i+1)^{-3/2}` for `2(i+1) ≤ n+1`. -/
theorem parkingGap_le {n i : ℕ} (h : 2 * (i + 1) ≤ n + 1) :
    parkingGap n i ≤ 2 / (((i : ℝ) + 1) * √((i : ℝ) + 1)) := by
  obtain ⟨he, hq0, hq, -, -, hR1, hR2, hsum, hab, ha⟩ := parkingGap_factor_bounds h
  rw [he]
  have hS : 3 / 2 ≤ √(2 * Real.pi) :=
    (Real.le_sqrt' (by norm_num)).2 (by nlinarith [Real.two_le_pi])
  have hsa : 1 ≤ √((i : ℝ) + 1) := Real.one_le_sqrt.2 ha
  generalize borelWeight (i + 1) = q at *
  generalize borelWeight (n - i) / borelWeight (n + 1) = R at *
  generalize ((n - i : ℕ) : ℝ) = b at *
  generalize (n : ℝ) + 1 = N at *
  generalize √(2 * Real.pi) = S at *
  generalize √((i : ℝ) + 1) = sa at *
  generalize (i : ℝ) + 1 = a at *
  have ha0 : 0 < a := by linarith
  have hsa0 : 0 < sa := by linarith
  have hS0 : 0 < S := by linarith
  have hb0 : 0 < b := by linarith
  have hR3 : R ≤ 3 := by
    have : 2 * N / b ≤ 4 := by
      rw [div_le_iff₀ hb0]
      linarith
    linarith
  have hR0 : 0 ≤ R := by
    have : 1 / (12 * b) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  calc q * R ≤ 1 / (S * a * sa) * 3 := mul_le_mul hq hR3 hR0 (by positivity)
    _ ≤ 2 / (a * sa) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ a * sa)]

/-- Lower bound `(i+1)^{-3/2} / 4 ≤ δ_n(i + 1)` for `2(i+1) ≤ n+1`. -/
theorem le_parkingGap {n i : ℕ} (h : 2 * (i + 1) ≤ n + 1) :
    1 / (4 * ((i : ℝ) + 1) * √((i : ℝ) + 1)) ≤ parkingGap n i := by
  obtain ⟨he, hq0, -, -, hq', hR1, -, hsum, hab, ha⟩ := parkingGap_factor_bounds h
  rw [he]
  have hS3 : √(2 * Real.pi) ≤ 3 :=
    (Real.sqrt_le_left (by norm_num)).2 (by nlinarith [Real.pi_le_four])
  have hS0 : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsa : 1 ≤ √((i : ℝ) + 1) := Real.one_le_sqrt.2 ha
  generalize borelWeight (i + 1) = q at *
  generalize borelWeight (n - i) / borelWeight (n + 1) = R at *
  generalize ((n - i : ℕ) : ℝ) = b at *
  generalize (n : ℝ) + 1 = N at *
  generalize √(2 * Real.pi) = S at *
  generalize √((i : ℝ) + 1) = sa at *
  generalize (i : ℝ) + 1 = a at *
  have ha0 : 0 < a := by linarith
  have hsa0 : 0 < sa := by linarith
  have hb0 : 0 < b := by linarith
  have hp0 : 0 ≤ 1 / (S * a * sa) := by positivity
  have hR : 11 / 12 ≤ R := by
    have : 1 / (12 * b) ≤ 1 / 12 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hq : 11 / 12 * (1 / (S * a * sa)) ≤ q := by
    have : 1 / (12 * a) ≤ 1 / 12 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h1 : 11 / 12 * (1 / (S * a * sa)) ≤ (1 - 1 / (12 * a)) * (1 / (S * a * sa)) :=
      mul_le_mul_of_nonneg_right (by linarith) hp0
    linarith
  calc 1 / (4 * a * sa) ≤ 11 / 12 * (1 / (S * a * sa)) * (11 / 12) := by
        rw [show 11 / 12 * (1 / (S * a * sa)) * (11 / 12) = 121 / (144 * (S * a * sa)) by ring,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hS3 (by positivity : (0 : ℝ) ≤ a * sa)]
    _ ≤ q * R := mul_le_mul hq hR (by norm_num) hq0.le

/-- Asymptotics of the gaps: for `2(i+1) ≤ n+1`,
`|δ_n(i + 1) - (2π)^{-1/2} (i+1)^{-3/2}| ≤ (2π)^{-1/2} (i+1)^{-1/2} (1/(12 (i+1)^2) + 4/(n+1))`.
This is the estimate `δ_n(i) = q_i (1 + O(i/n))`, `q_i = (2π)^{-1/2} i^{-3/2} + O(i^{-5/2})`
of `lem:marginal`. -/
theorem abs_parkingGap_sub_le {n i : ℕ} (h : 2 * (i + 1) ≤ n + 1) :
    |parkingGap n i - 1 / (√(2 * Real.pi) * ((i : ℝ) + 1) * √((i : ℝ) + 1))| ≤
      1 / (12 * √(2 * Real.pi) * ((i : ℝ) + 1) ^ 2 * √((i : ℝ) + 1)) +
        4 / (√(2 * Real.pi) * ((n : ℝ) + 1) * √((i : ℝ) + 1)) := by
  obtain ⟨he, hq0, hq, hpq, -, hR1, hR2, hsum, hab, ha⟩ := parkingGap_factor_bounds h
  rw [he]
  have hS0 : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hsa : 1 ≤ √((i : ℝ) + 1) := Real.one_le_sqrt.2 ha
  generalize borelWeight (i + 1) = q at *
  generalize borelWeight (n - i) / borelWeight (n + 1) = R at *
  generalize ((n - i : ℕ) : ℝ) = b at *
  generalize (n : ℝ) + 1 = N at *
  generalize √(2 * Real.pi) = S at *
  generalize √((i : ℝ) + 1) = sa at *
  generalize (i : ℝ) + 1 = a at *
  have ha0 : 0 < a := by linarith
  have hsa0 : 0 < sa := by linarith
  have hb0 : 0 < b := by linarith
  have hN0 : 0 < N := by linarith
  have hp0 : 0 ≤ 1 / (S * a * sa) := by positivity
  have hE1 : 0 ≤ 1 / (12 * S * a ^ 2 * sa) := by positivity
  have hR0 : 0 ≤ R := by
    have : 1 / (12 * b) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have c1 : 1 / (S * a * sa) * (2 * N / b - 2) ≤ 4 / (S * N * sa) := by
    rw [← hsum]
    have e : 1 / (S * a * sa) * (2 * (b + a) / b - 2) = 2 / (S * b * sa) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hab (by positivity : (0 : ℝ) ≤ S * sa)]
  have c2 : 1 / (S * a * sa) * (1 / (12 * b)) ≤ 4 / (S * N * sa) := by
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have hN48 : N ≤ 48 * a * b := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hN48 (by positivity : (0 : ℝ) ≤ S * sa)]
  have hqR : q * R ≤ 1 / (S * a * sa) * R := mul_le_mul_of_nonneg_right hq hR0
  have hpR : 1 / (S * a * sa) * R ≤ 1 / (S * a * sa) * (2 * N / b - 1) :=
    mul_le_mul_of_nonneg_left hR2 hp0
  have hqR1 : q * (1 - 1 / (12 * b)) ≤ q * R := mul_le_mul_of_nonneg_left hR1 hq0.le
  have hq12 : q * (1 / (12 * b)) ≤ 1 / (S * a * sa) * (1 / (12 * b)) :=
    mul_le_mul_of_nonneg_right hq (by positivity)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end Parking

end
