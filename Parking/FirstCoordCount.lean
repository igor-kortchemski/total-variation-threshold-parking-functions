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

public import Parking.Breakpoint
public import Parking.Law
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# The law of the first preference of a parking function

This module proves [DH17, Corollary 1],
for `lem:marginal` of the source paper, and the value `N(1)` that gives
`g_n(1) = (n - 1)/(n + 1)` without Abel's identity.

Letters are `0`-based, as in `Parking.Basic`. For a parking function of length `N + 1`,
`firstValueCount N t` counts those whose first letter is `t`, and
`card_firstCoord_eq_firstValueCount` identifies it with the count of the law `μ_n` of
`Parking.Law`. The gap count `gapCount N i = (N choose i) · P(i) · P(N - i)`, with
`P(t) = (t + 1)^(t - 1)`, is the breakpoint count of `Parking.Breakpoint`.

* Raising the first letter from `t` to `t + 1` changes only the number of letters below
  `t + 1` (`isParkingFn_cons_succ_iff`). The parking functions lost are those with exactly
  `t + 1` letters below `t + 1`. Removing their first letter `t` and closing the gap at
  `t` (`card_cons_breakpoint`) gives the parking functions of length `N` with exactly `t`
  letters below `t`. Hence `firstValueCount N t = firstValueCount N (t + 1) + gapCount N t`
  (`firstValueCount_eq_add`) and `firstValueCount N t = ∑_{t ≤ i ≤ N} gapCount N i`
  (`firstValueCount_eq_sum`).
* Summing over `t` gives `∑_i (i + 1) · gapCount N i = (N + 2)^N`. With the symmetry
  `gapCount N (N - i) = gapCount N i` (`gapCount_symm`), the reflection of this sum gives
  `firstValueCount N 0 · (N + 2) = 2 (N + 2)^N` (`firstValueCount_zero_mul`).
-/

public section

namespace Parking

open Finset

/-- The number of parking functions of length `N + 1` whose first letter is `t`
(`0`-based letters). -/
@[expose] def firstValueCount (N t : ℕ) : ℕ :=
  #{a : Fin (N + 1) → Fin (N + 1) | IsParkingFn a ∧ (a 0 : ℕ) = t}

/-- The gap count `(N choose i) · P(i) · P(N - i)`, with `P = parkingFnCount`. By the
breakpoint lemma it is the number of parking functions of length `N` with exactly `i`
letters below `i`. -/
@[expose] def gapCount (N i : ℕ) : ℕ := N.choose i * parkingFnCount i * parkingFnCount (N - i)

/-- The parking condition in terms of the numbers of letters below each level: a word of
length `m` is a parking function if and only if, for every `ℓ ≤ m`, at least `ℓ` of its
letters are smaller than `ℓ`. -/
theorem isParkingFn_iff_le_card {m : ℕ} (a : Fin m → Fin m) :
    IsParkingFn a ↔ ∀ ℓ ≤ m, ℓ ≤ #{i | (a i : ℕ) < ℓ} := by
  constructor
  · intro h ℓ hℓ
    rcases ℓ with _ | s
    · exact Nat.zero_le _
    · have hs := h ⟨s, by omega⟩
      have e : #{i | a i ≤ (⟨s, by omega⟩ : Fin m)} = #{i | (a i : ℕ) < s + 1} := by
        congr 1
      rw [e] at hs
      exact hs
  · intro h j
    have hj := h (j + 1) j.isLt
    have e : #{i | a i ≤ j} = #{i | (a i : ℕ) < j + 1} := by
      congr 1
    rw [e]
    exact hj

/-- The number of letters below `ℓ` of `Fin.cons x w` is that of `w`, plus one if
`x < ℓ`. -/
theorem card_filter_cons_lt {N : ℕ} (x : Fin (N + 1)) (w : Fin N → Fin (N + 1)) (ℓ : ℕ) :
    #{i | ((Fin.cons x w : Fin (N + 1) → Fin (N + 1)) i : ℕ) < ℓ} =
      (if (x : ℕ) < ℓ then 1 else 0) + #{k | (w k : ℕ) < ℓ} := by
  simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- The parking condition for `Fin.cons x w`, in terms of the letters of `w` below each
level. -/
theorem isParkingFn_cons_iff {N : ℕ} (x : Fin (N + 1)) (w : Fin N → Fin (N + 1)) :
    IsParkingFn (Fin.cons x w : Fin (N + 1) → Fin (N + 1)) ↔
      ∀ ℓ ≤ N + 1, ℓ ≤ (if (x : ℕ) < ℓ then 1 else 0) + #{k | (w k : ℕ) < ℓ} := by
  simp only [isParkingFn_iff_le_card, card_filter_cons_lt]

/-- Removing the first letter `x`: `firstValueCount N x` counts the words `w` of length
`N` such that `Fin.cons x w` is a parking function. -/
theorem firstValueCount_eq_card_cons {N : ℕ} (x : Fin (N + 1)) :
    firstValueCount N x =
      #{w : Fin N → Fin (N + 1) | IsParkingFn (Fin.cons x w : Fin (N + 1) → Fin (N + 1))} := by
  rw [firstValueCount]
  apply Finset.card_nbij' (fun a => Fin.tail a)
    (fun w => (Fin.cons x w : Fin (N + 1) → Fin (N + 1)))
  · intro a ha
    simp only [mem_coe, mem_filter, mem_univ, true_and] at ha ⊢
    have h0 : a 0 = x := Fin.ext ha.2
    rw [← h0, Fin.cons_self_tail]
    exact ha.1
  · intro w hw
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hw ⊢
    exact ⟨hw, by rw [Fin.cons_zero]⟩
  · intro a ha
    simp only [mem_coe, mem_filter, mem_univ, true_and] at ha
    have h0 : a 0 = x := Fin.ext ha.2
    simp only
    rw [← h0, Fin.cons_self_tail]
  · intro w _
    exact Fin.tail_cons _ _

/-- There is no parking function of length `N + 1` with first letter `t > N`. -/
theorem firstValueCount_eq_zero {N t : ℕ} (h : N < t) : firstValueCount N t = 0 := by
  rw [firstValueCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  have := (a 0).isLt
  omega

/-- Raising the first letter from `t` to `t + 1` keeps a parking function exactly when
at least `t + 1` of the other letters are below `t + 1`. -/
theorem isParkingFn_cons_succ_iff {N : ℕ} (x : Fin (N + 1)) (hx : (x : ℕ) + 1 < N + 1)
    (w : Fin N → Fin (N + 1)) :
    IsParkingFn (Fin.cons (⟨x + 1, hx⟩ : Fin (N + 1)) w : Fin (N + 1) → Fin (N + 1)) ↔
      IsParkingFn (Fin.cons x w : Fin (N + 1) → Fin (N + 1)) ∧
        (x : ℕ) + 1 ≤ #{k | (w k : ℕ) < x + 1} := by
  simp only [isParkingFn_cons_iff]
  constructor
  · intro h
    refine ⟨fun ℓ hℓ => ?_, ?_⟩
    · have h1 := h ℓ hℓ
      split_ifs at h1 ⊢ <;> omega
    · have h1 := h (x + 1) hx.le
      simpa only [lt_self_iff_false, ite_false, zero_add] using h1
  · rintro ⟨h, hc⟩ ℓ hℓ
    by_cases hℓx : ℓ = (x : ℕ) + 1
    · subst hℓx
      simpa only [lt_self_iff_false, ite_false, zero_add] using hc
    · have h1 := h ℓ hℓ
      split_ifs at h1 ⊢ <;> omega

/-- The value of `p.succAbove i`: it is `i` below the pivot and `i + 1` from the pivot
on. -/
theorem val_succAbove_eq_ite {N : ℕ} (p : Fin (N + 1)) (i : Fin N) :
    (p.succAbove i : ℕ) = if (i : ℕ) < p then (i : ℕ) else (i : ℕ) + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by rw [Fin.lt_def, Fin.val_castSucc]; exact h2)
  · exact absurd (by rw [Fin.lt_def, Fin.val_castSucc]; exact h2) h1
  · rfl

/-- Closing the gap at the first letter `x`: for every word `z` of length `N`, the word
`Fin.cons x (x.succAbove ∘ z)` is a parking function exactly when `z` is. -/
theorem isParkingFn_cons_succAbove_iff {N : ℕ} (x : Fin (N + 1)) (z : Fin N → Fin N) :
    IsParkingFn (Fin.cons x (fun k => x.succAbove (z k)) : Fin (N + 1) → Fin (N + 1)) ↔
      IsParkingFn z := by
  have hlow : ∀ ℓ : ℕ, ℓ ≤ x →
      #{k | (x.succAbove (z k) : ℕ) < ℓ} = #{k | (z k : ℕ) < ℓ} := by
    intro ℓ hℓ
    congr 1
    apply filter_congr
    intro k _
    rw [val_succAbove_eq_ite]
    split_ifs <;> omega
  have hhigh : ∀ ℓ : ℕ, (x : ℕ) < ℓ →
      #{k | (x.succAbove (z k) : ℕ) < ℓ} = #{k | (z k : ℕ) < ℓ - 1} := by
    intro ℓ hℓ
    congr 1
    apply filter_congr
    intro k _
    rw [val_succAbove_eq_ite]
    split_ifs <;> omega
  rw [isParkingFn_cons_iff, isParkingFn_iff_le_card]
  constructor
  · intro h ℓ hℓ
    by_cases hℓx : ℓ ≤ x
    · have h1 := h ℓ (by omega)
      rw [hlow ℓ hℓx, ite_eq_right (by omega), zero_add] at h1
      exact h1
    · have h1 := h (ℓ + 1) (by omega)
      rw [hhigh (ℓ + 1) (by omega), ite_eq_left (by omega), Nat.add_sub_cancel] at h1
      omega
  · intro h ℓ hℓ
    by_cases hℓx : ℓ ≤ x
    · rw [hlow ℓ hℓx, ite_eq_right (by omega), zero_add]
      exact h ℓ (by have := x.isLt; omega)
    · rw [hhigh ℓ (by omega), ite_eq_left (by omega)]
      have h1 := h (ℓ - 1) (by omega)
      omega

/-- A parking function `Fin.cons x w` has at least `x` letters below `x` among the
letters of `w`. -/
theorem le_card_of_isParkingFn_cons {N : ℕ} {x : Fin (N + 1)} {w : Fin N → Fin (N + 1)}
    (h : IsParkingFn (Fin.cons x w : Fin (N + 1) → Fin (N + 1))) :
    (x : ℕ) ≤ #{k | (w k : ℕ) < x} := by
  have h1 := (isParkingFn_cons_iff x w).1 h x (by have := x.isLt; omega)
  rwa [ite_eq_right (lt_irrefl _), zero_add] at h1

/-- The words `w` such that `Fin.cons x w` is a parking function with exactly `x` letters
of `w` below `x + 1` are the words `x.succAbove ∘ z`, for the parking functions `z` of
length `N` with exactly `x` letters below `x`. -/
theorem card_cons_breakpoint {N : ℕ} (x : Fin (N + 1)) :
    #{w : Fin N → Fin (N + 1) | IsParkingFn (Fin.cons x w : Fin (N + 1) → Fin (N + 1)) ∧
        #{k | (w k : ℕ) < x + 1} = x} = breakpointCount N x := by
  have hcount : ∀ z : Fin N → Fin N,
      #{k | (x.succAbove (z k) : ℕ) < x + 1} = #{k | (z k : ℕ) < x} := by
    intro z
    congr 1
    apply filter_congr
    intro k _
    rw [val_succAbove_eq_ite]
    split_ifs <;> omega
  rw [breakpointCount]
  symm
  apply Finset.card_bij (fun z _ => fun k => x.succAbove (z k))
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact ⟨(isParkingFn_cons_succAbove_iff x z).2 hz.1, by rw [hcount, hz.2]⟩
  · intro z _ z' _ h
    funext k
    exact Fin.succAbove_right_injective (congrFun h k)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    obtain ⟨hP, hc⟩ := hw
    have hne : ∀ k, w k ≠ x := by
      intro k₀ hk₀
      have hlow := le_card_of_isParkingFn_cons hP
      have hsub : insert k₀ ({k | (w k : ℕ) < x} : Finset (Fin N)) ⊆
          ({k | (w k : ℕ) < x + 1} : Finset (Fin N)) := by
        intro k hk
        rw [mem_insert, mem_filter] at hk
        rw [mem_filter]
        rcases hk with rfl | hk
        · rw [hk₀]
          exact ⟨mem_univ _, Nat.lt_succ_self _⟩
        · exact ⟨mem_univ _, by omega⟩
      have hnot : k₀ ∉ ({k | (w k : ℕ) < x} : Finset (Fin N)) := by
        rw [mem_filter, hk₀]
        exact fun h => lt_irrefl _ h.2
      have h1 := card_le_card hsub
      rw [card_insert_of_notMem hnot, hc] at h1
      omega
    choose z hz using fun k => Fin.exists_succAbove_eq (hne k)
    have hw : (fun k => x.succAbove (z k)) = w := funext hz
    refine ⟨z, ?_, hw⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [← isParkingFn_cons_succAbove_iff x z, hw, ← hcount]
    simp only [hz]
    exact ⟨hP, hc⟩

/-- DH17, Corollary 1, in recursive form: lowering the first letter from `t + 1` to `t`
adds the `gapCount N t` parking functions with exactly `t + 1` letters below `t + 1`. -/
theorem firstValueCount_eq_add {N t : ℕ} (ht : t ≤ N) :
    firstValueCount N t = firstValueCount N (t + 1) + gapCount N t := by
  obtain ⟨x, rfl⟩ : ∃ x : Fin (N + 1), (x : ℕ) = t := ⟨⟨t, by omega⟩, rfl⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := ({w | IsParkingFn (Fin.cons x w : Fin (N + 1) → Fin (N + 1))} :
      Finset (Fin N → Fin (N + 1))))
    (fun w => (x : ℕ) + 1 ≤ #{k | (w k : ℕ) < x + 1})
  rw [filter_filter, filter_filter] at hsplit
  rw [firstValueCount_eq_card_cons x, ← hsplit]
  congr 1
  · rcases Nat.lt_or_ge (x : ℕ) N with hlt | hge
    · have e : firstValueCount N ((x : ℕ) + 1) = _ :=
        firstValueCount_eq_card_cons (⟨x + 1, by omega⟩ : Fin (N + 1))
      rw [e]
      congr 1
      apply filter_congr
      intro w _
      exact (isParkingFn_cons_succ_iff x (by omega) w).symm
    · rw [firstValueCount_eq_zero (by omega), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _ hw
      have h1 := card_filter_le (univ : Finset (Fin N)) (fun k => (w k : ℕ) < x + 1)
      rw [card_univ, Fintype.card_fin] at h1
      omega
  · rw [gapCount, ← breakpointCount_eq ht, ← card_cons_breakpoint]
    congr 1
    apply filter_congr
    intro w _
    constructor
    · rintro ⟨hP, hc⟩
      refine ⟨hP, ?_⟩
      have h1 := (isParkingFn_cons_iff x w).1 hP (x + 1) (by omega)
      rw [ite_eq_left (Nat.lt_succ_self _)] at h1
      omega
    · rintro ⟨hP, hc⟩
      exact ⟨hP, by omega⟩

/-- The first-letter counts decrease: `firstValueCount N (t + 1) ≤ firstValueCount N t`. -/
theorem firstValueCount_succ_le (N t : ℕ) :
    firstValueCount N (t + 1) ≤ firstValueCount N t := by
  rcases Nat.lt_or_ge N t with h | h
  · rw [firstValueCount_eq_zero (by omega)]
    exact Nat.zero_le _
  · rw [firstValueCount_eq_add h]
    exact Nat.le_add_right _ _

/-- DH17, Corollary 1: the number of parking functions of length `N + 1` with first
letter `t` is `∑_{t ≤ i ≤ N} gapCount N i`. -/
theorem firstValueCount_eq_sum (N t : ℕ) :
    firstValueCount N t = ∑ i ∈ Finset.Ico t (N + 1), gapCount N i := by
  induction h : N + 1 - t generalizing t with
  | zero =>
    rw [firstValueCount_eq_zero (by omega), Finset.Ico_eq_empty_of_le (by omega),
      Finset.sum_empty]
  | succ k ih =>
    rw [firstValueCount_eq_add (by omega), ih (t + 1) (by omega),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : t < N + 1), add_comm]

/-- The gap count in closed form: `gapCount N i = (N choose i) (i + 1)^(i - 1)
(N - i + 1)^(N - i - 1)`. -/
theorem gapCount_eq (N i : ℕ) :
    gapCount N i = N.choose i * (i + 1) ^ (i - 1) * (N - i + 1) ^ (N - i - 1) := by
  rw [gapCount, parkingFnCount_eq, parkingFnCount_eq]

/-- The gap counts are symmetric: `gapCount N (N - i) = gapCount N i`. -/
theorem gapCount_symm {N i : ℕ} (hi : i ≤ N) : gapCount N (N - i) = gapCount N i := by
  rw [gapCount, gapCount, Nat.choose_symm hi, Nat.sub_sub_self hi, mul_assoc, mul_assoc,
    mul_comm (parkingFnCount (N - i))]

/-- Summing the first-letter counts over all first letters counts all the parking
functions of length `N + 1`: `∑_t firstValueCount N t = (N + 2)^N`. -/
theorem sum_firstValueCount (N : ℕ) :
    ∑ t ∈ range (N + 1), firstValueCount N t = (N + 2) ^ N := by
  have h : parkingFnCount (N + 1) = ∑ x : Fin (N + 1), firstValueCount N x := by
    rw [parkingFnCount, card_eq_sum_card_fiberwise (f := fun a => a 0) (t := univ)
      (fun _ _ => mem_coe.2 (mem_univ _))]
    refine sum_congr rfl fun x _ => ?_
    rw [firstValueCount, filter_filter]
    congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun t => firstValueCount N t), ← h, parkingFnCount_eq]
  simp only [Nat.add_sub_cancel]

/-- The first-letter count at `0`: `firstValueCount N 0 · (N + 2) = 2 (N + 2)^N`, that is
`N(1) · (n + 1) = 2 (n + 1)^(n - 1)` for `n = N + 1`. The proof uses the symmetry of the gap counts,
not Abel's identity. -/
theorem firstValueCount_zero_mul (N : ℕ) :
    firstValueCount N 0 * (N + 2) = 2 * (N + 2) ^ N := by
  have hW : ∑ i ∈ range (N + 1), (i + 1) * gapCount N i = (N + 2) ^ N := by
    rw [← sum_firstValueCount]
    simp_rw [firstValueCount_eq_sum]
    rw [Finset.sum_comm' (t' := range (N + 1)) (s' := fun i => range (i + 1))]
    · refine sum_congr rfl fun i _ => ?_
      rw [sum_const, card_range, smul_eq_mul]
    · intro t i
      simp only [mem_range, mem_Ico]
      omega
  have hR : ∑ i ∈ range (N + 1), (i + 1) * gapCount N i =
      ∑ i ∈ range (N + 1), (N - i + 1) * gapCount N i := by
    rw [← sum_range_reflect (fun i => (i + 1) * gapCount N i) (N + 1)]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [show N + 1 - 1 - i = N - i by omega, gapCount_symm (by omega)]
  have hS : firstValueCount N 0 = ∑ i ∈ range (N + 1), gapCount N i := by
    rw [firstValueCount_eq_sum, Nat.Ico_zero_eq_range]
  calc firstValueCount N 0 * (N + 2)
      = ∑ i ∈ range (N + 1), ((i + 1) * gapCount N i + (N - i + 1) * gapCount N i) := by
        rw [hS, sum_mul]
        refine sum_congr rfl fun i hi => ?_
        rw [mem_range] at hi
        rw [← add_mul, mul_comm]
        congr 1
        omega
    _ = 2 * (N + 2) ^ N := by
        rw [sum_add_distrib, ← hR, hW, two_mul]

/-- The first-letter count at the last letter: `firstValueCount N N = (N + 1)^(N - 1)`. -/
theorem firstValueCount_self (N : ℕ) : firstValueCount N N = (N + 1) ^ (N - 1) := by
  rw [firstValueCount_eq_add le_rfl, firstValueCount_eq_zero (Nat.lt_succ_self N), zero_add,
    gapCount_eq, Nat.choose_self, Nat.sub_self]
  simp only [one_mul, zero_tsub, pow_zero, mul_one]

/-- Transport of `firstValueCount` along `m = N + 1`. -/
theorem card_isParkingFn_val_zero_eq {m N : ℕ} (hm : 0 < m) (h : m = N + 1) (t : ℕ) :
    #{a : Fin m → Fin m | IsParkingFn a ∧ (a ⟨0, hm⟩ : ℕ) = t} = firstValueCount N t := by
  subst h
  rfl

/-- The law `μ_n` of the first coordinate of a uniform parking function of size `n`
counts `firstValueCount (n - 1) j` parking functions at the value `j`. -/
theorem card_firstCoord_eq_firstValueCount (n : ℕ+) (j : Fin n) :
    #{a : ParkingFunction n | firstCoord n a = j} = firstValueCount ((n : ℕ) - 1) j := by
  rw [← card_isParkingFn_val_zero_eq n.pos (by have := n.pos; omega)]
  apply Finset.card_bij (fun a _ => a.1)
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact ⟨a.2, congrArg Fin.val ha⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    exact ⟨⟨b, hb.1⟩, mem_filter.2 ⟨mem_univ _, Fin.ext hb.2⟩, rfl⟩

end Parking

end
