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

public import Parking.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
import Parking.Count
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum

/-!
# The breakpoint lemma for parking functions

This module provides the counting argument for the elementary
proof of [DH17, Corollary 1] used by `lem:marginal` of the source paper.

The parking condition of `Parking.Basic` is restated as `IsParkingFn` for words of every
length `m : ℕ`, including the empty word, and `parkingFnCount m = (m + 1)^(m - 1)`
(`parkingFnCount_eq`). The concatenation `joinWord x y` of a word `x` of length `ℓ` with
the word `y` of length `r` shifted by `ℓ` is a parking function exactly when `x` and `y`
are (`isParkingFn_joinWord_iff`). Hence the parking functions of length `ℓ + r` whose
letters below `ℓ` occupy a prescribed set of `ℓ` positions are counted by
`parkingFnCount ℓ * parkingFnCount r` (`card_isParkingFn_lowSet`), and the breakpoint
lemma follows by summing over that set:

`#{z ∈ PF_m : exactly ℓ letters of z are < ℓ} = (m choose ℓ) · P(ℓ) · P(m - ℓ)`,

with `P(t) = (t + 1)^(t - 1)` (`breakpointCount_eq`). Letters are `0`-based, as in
`Parking.Basic`: the Lean letter `a i` is the preference `a i + 1`.
-/

public section

namespace Parking

open Finset

/-- A word `a : Fin m → Fin m` of any length `m`, including `0`, is a parking function if
for every `j`, at least `j + 1` of its letters are at most `j`. This is the condition
`isParkingFunction` of `Parking.Basic`, without the positivity of the length. -/
@[expose] def IsParkingFn {m : ℕ} (a : Fin m → Fin m) : Prop :=
  ∀ j : Fin m, j.val + 1 ≤ #{i | a i ≤ j}

/-- The parking condition is decidable, as a finite conjunction of inequalities between
natural numbers. -/
instance instDecidablePredIsParkingFn {m : ℕ} : DecidablePred (IsParkingFn (m := m)) :=
  fun a =>
    inferInstanceAs (Decidable (∀ j : Fin m, j.val + 1 ≤ #{i | a i ≤ j}))

/-- The number of parking functions of length `m`. -/
@[expose] def parkingFnCount (m : ℕ) : ℕ := #{a : Fin m → Fin m | IsParkingFn a}

/-- The concatenation of a word `x` of length `ℓ` with the word `y` of length `r` shifted
by `ℓ`: the result has letters `x k` at the positions `k < ℓ` and letters `ℓ + y k` at the
positions `ℓ + k`. -/
@[expose] def joinWord {ℓ r : ℕ} (x : Fin ℓ → Fin ℓ) (y : Fin r → Fin r) :
    Fin (ℓ + r) → Fin (ℓ + r) :=
  Fin.append (fun k => Fin.castAdd r (x k)) (fun k => Fin.natAdd ℓ (y k))

/-- The number of parking functions of length `m` with exactly `ℓ` letters smaller than
`ℓ` (in the `0`-based letters of `Parking.Basic`). -/
@[expose] def breakpointCount (m ℓ : ℕ) : ℕ :=
  #{z : Fin m → Fin m | IsParkingFn z ∧ #{k | (z k : ℕ) < ℓ} = ℓ}

/-- For a positive length, `IsParkingFn` is the condition `isParkingFunction` of
`Parking.Basic`. -/
theorem isParkingFunction_iff_isParkingFn {n : ℕ+} (a : Fin n → Fin n) :
    isParkingFunction a ↔ IsParkingFn a :=
  Iff.rfl

/-- Konheim–Weiss for every length: there are `(m + 1)^(m - 1)` parking functions of
length `m`. For `m = 0` the empty word is the only word, and it is a parking function. -/
theorem parkingFnCount_eq (m : ℕ) : parkingFnCount m = (m + 1) ^ (m - 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [parkingFnCount, Finset.filter_true_of_mem (fun a _ j => j.elim0), Finset.card_univ]
    simp only [Fintype.card_unique, zero_add, zero_tsub, pow_zero]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ+, (n : ℕ) = m := ⟨⟨m, hm⟩, rfl⟩
    have e : ParkingFunction n ≃ {a : Fin n → Fin n // IsParkingFn a} :=
      Equiv.subtypeEquivRight fun a => isParkingFunction_iff_isParkingFn a
    rw [parkingFnCount, ← Fintype.card_subtype, ← Fintype.card_congr e, card_parkingFunction]

/-- The parking condition is invariant under every permutation of the positions. -/
theorem isParkingFn_comp_perm_iff {m : ℕ} (a : Fin m → Fin m) (σ : Equiv.Perm (Fin m)) :
    IsParkingFn (a ∘ σ) ↔ IsParkingFn a := by
  have h : ∀ j, #{i | (a ∘ σ) i ≤ j} = #{i | a i ≤ j} := fun j =>
    Finset.card_equiv σ fun i => by
      simp only [mem_filter, mem_univ, true_and, Function.comp_apply]
  simp only [IsParkingFn, h]

/-- Counting the positions of `Fin (ℓ + r)` that satisfy a predicate splits into the first
`ℓ` positions and the last `r` positions. -/
theorem card_filter_fin_add {ℓ r : ℕ} (p : Fin (ℓ + r) → Prop) [DecidablePred p] :
    #{k | p k} = #{k : Fin ℓ | p (Fin.castAdd r k)} + #{k : Fin r | p (Fin.natAdd ℓ k)} := by
  simp only [Finset.card_filter, Fin.sum_univ_add]

/-- The first `ℓ` letters of `joinWord x y` are the letters of `x`. -/
@[simp] theorem joinWord_castAdd {ℓ r : ℕ} (x : Fin ℓ → Fin ℓ) (y : Fin r → Fin r)
    (k : Fin ℓ) : joinWord x y (Fin.castAdd r k) = Fin.castAdd r (x k) := by
  simp only [joinWord, Fin.append_left]

/-- The last `r` letters of `joinWord x y` are the letters of `y`, shifted by `ℓ`. -/
@[simp] theorem joinWord_natAdd {ℓ r : ℕ} (x : Fin ℓ → Fin ℓ) (y : Fin r → Fin r)
    (k : Fin r) : joinWord x y (Fin.natAdd ℓ k) = Fin.natAdd ℓ (y k) := by
  simp only [joinWord, Fin.append_right]

/-- Below a level `j < ℓ`, the letters of `joinWord x y` are those of `x`. -/
theorem card_joinWord_le_castAdd {ℓ r : ℕ} (x : Fin ℓ → Fin ℓ) (y : Fin r → Fin r)
    (j : Fin ℓ) : #{i | joinWord x y i ≤ Fin.castAdd r j} = #{k | x k ≤ j} := by
  rw [card_filter_fin_add]
  have h0 : #{k : Fin r | joinWord x y (Fin.natAdd ℓ k) ≤ Fin.castAdd r j} = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _ hk
    rw [joinWord_natAdd, Fin.le_iff_val_le_val, Fin.val_natAdd, Fin.val_castAdd] at hk
    have := j.isLt
    omega
  rw [h0, add_zero]
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [joinWord_castAdd, Fin.le_iff_val_le_val, Fin.le_iff_val_le_val, Fin.val_castAdd,
    Fin.val_castAdd]

/-- Below a level `ℓ + j`, the letters of `joinWord x y` are all the `ℓ` letters of `x`
and the letters of `y` that are at most `j`. -/
theorem card_joinWord_le_natAdd {ℓ r : ℕ} (x : Fin ℓ → Fin ℓ) (y : Fin r → Fin r)
    (j : Fin r) : #{i | joinWord x y i ≤ Fin.natAdd ℓ j} = ℓ + #{k | y k ≤ j} := by
  rw [card_filter_fin_add]
  have hℓ : #{k : Fin ℓ | joinWord x y (Fin.castAdd r k) ≤ Fin.natAdd ℓ j} = ℓ := by
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro k _
    rw [joinWord_castAdd, Fin.le_iff_val_le_val, Fin.val_natAdd, Fin.val_castAdd]
    have := (x k).isLt
    omega
  rw [hℓ]
  congr 2
  apply Finset.filter_congr
  intro k _
  rw [joinWord_natAdd, Fin.le_iff_val_le_val, Fin.le_iff_val_le_val, Fin.val_natAdd,
    Fin.val_natAdd]
  omega

/-- The concatenation `joinWord x y` is a parking function exactly when both `x` and `y`
are parking functions. -/
theorem isParkingFn_joinWord_iff {ℓ r : ℕ} (x : Fin ℓ → Fin ℓ) (y : Fin r → Fin r) :
    IsParkingFn (joinWord x y) ↔ IsParkingFn x ∧ IsParkingFn y := by
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have hj := h (Fin.castAdd r j)
      rwa [card_joinWord_le_castAdd, Fin.val_castAdd] at hj
    · have hj := h (Fin.natAdd ℓ j)
      rw [card_joinWord_le_natAdd, Fin.val_natAdd] at hj
      omega
  · rintro ⟨hx, hy⟩ j
    induction j using Fin.addCases with
    | left j =>
      rw [card_joinWord_le_castAdd, Fin.val_castAdd]
      exact hx j
    | right j =>
      rw [card_joinWord_le_natAdd, Fin.val_natAdd]
      have := hy j
      omega

/-- The parking functions of length `ℓ + r` whose letters below `ℓ` are exactly at the
first `ℓ` positions are the words `joinWord x y` with `x`, `y` parking functions; there
are `parkingFnCount ℓ * parkingFnCount r` of them. -/
theorem card_isParkingFn_blocks (ℓ r : ℕ) :
    #{z : Fin (ℓ + r) → Fin (ℓ + r) | IsParkingFn z ∧ ∀ k, ((z k : ℕ) < ℓ ↔ (k : ℕ) < ℓ)} =
      parkingFnCount ℓ * parkingFnCount r := by
  rw [parkingFnCount, parkingFnCount, ← Finset.card_product]
  symm
  apply Finset.card_bij (fun p _ => joinWord p.1 p.2)
  · rintro ⟨x, y⟩ hxy
    simp only [mem_product, mem_filter, mem_univ, true_and] at hxy ⊢
    refine ⟨(isParkingFn_joinWord_iff x y).2 hxy, fun k => ?_⟩
    induction k using Fin.addCases with
    | left k =>
      rw [joinWord_castAdd, Fin.val_castAdd, Fin.val_castAdd]
      exact iff_of_true (x k).isLt k.isLt
    | right k =>
      rw [joinWord_natAdd, Fin.val_natAdd, Fin.val_natAdd]
      omega
  · rintro ⟨x, y⟩ _ ⟨x', y'⟩ _ h
    have h1 : x = x' := funext fun k => Fin.castAdd_injective _ _ <| by
      simpa only [joinWord_castAdd] using congrFun h (Fin.castAdd r k)
    have h2 : y = y' := funext fun k => Fin.natAdd_injective _ _ <| by
      simpa only [joinWord_natAdd] using congrFun h (Fin.natAdd ℓ k)
    rw [h1, h2]
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    obtain ⟨hz, hk⟩ := hz
    let x : Fin ℓ → Fin ℓ := fun k =>
      ⟨z (Fin.castAdd r k), (hk _).2 (by rw [Fin.val_castAdd]; exact k.isLt)⟩
    have hy : ∀ k : Fin r, (z (Fin.natAdd ℓ k) : ℕ) - ℓ < r := by
      intro k
      have h1 := (z (Fin.natAdd ℓ k)).isLt
      have h2 := k.isLt
      omega
    let y : Fin r → Fin r := fun k => ⟨z (Fin.natAdd ℓ k) - ℓ, hy k⟩
    have hxy : joinWord x y = z := by
      funext k
      induction k using Fin.addCases with
      | left k =>
        rw [joinWord_castAdd]
        exact Fin.ext rfl
      | right k =>
        rw [joinWord_natAdd]
        apply Fin.ext
        have h1 : ¬ (z (Fin.natAdd ℓ k) : ℕ) < ℓ := by
          rw [hk, Fin.val_natAdd]
          omega
        simp only [Fin.val_natAdd, y]
        omega
    refine ⟨(x, y), ?_, hxy⟩
    simp only [mem_product, mem_filter, mem_univ, true_and]
    rw [← isParkingFn_joinWord_iff, hxy]
    exact hz

/-- There are exactly `ℓ` positions of `Fin (ℓ + r)` below `ℓ`. -/
theorem card_val_lt (ℓ r : ℕ) : Fintype.card {k : Fin (ℓ + r) // (k : ℕ) < ℓ} = ℓ := by
  rw [Fintype.card_subtype, card_filter_fin_add]
  simp only [Fin.val_castAdd, Fin.is_lt, filter_true, card_univ, Fintype.card_fin, Fin.val_natAdd,
    add_lt_iff_neg_left, not_lt_zero, filter_false, card_empty, add_zero]

/-- For a set `S` of `ℓ` positions in `Fin (ℓ + r)`, some permutation of the positions
sends the first `ℓ` positions onto `S`. -/
theorem exists_perm_mem_iff_lt (ℓ r : ℕ) (S : Finset (Fin (ℓ + r))) (hS : #S = ℓ) :
    ∃ σ : Equiv.Perm (Fin (ℓ + r)), ∀ k, σ k ∈ S ↔ (k : ℕ) < ℓ := by
  have h1 : Fintype.card {k : Fin (ℓ + r) // (k : ℕ) < ℓ} =
      Fintype.card {k : Fin (ℓ + r) // k ∈ S} := by
    rw [card_val_lt, Fintype.card_coe, hS]
  have h2 : Fintype.card {k : Fin (ℓ + r) // ¬ (k : ℕ) < ℓ} =
      Fintype.card {k : Fin (ℓ + r) // k ∉ S} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  let e := Fintype.equivOfCardEq h1
  let f := Fintype.equivOfCardEq h2
  refine ⟨Equiv.subtypeCongr e f, fun k => ?_⟩
  by_cases hk : (k : ℕ) < ℓ
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_pos (p := fun x : Fin (ℓ + r) => (x : ℕ) < ℓ) hk,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl, hk, iff_true]
    exact (e ⟨k, hk⟩).2
  · simp only [Equiv.subtypeCongr, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_neg (p := fun x : Fin (ℓ + r) => (x : ℕ) < ℓ) hk,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr, hk, iff_false]
    exact (f ⟨k, hk⟩).2

/-- For every set `S` of `ℓ` positions in `Fin (ℓ + r)`, there are
`parkingFnCount ℓ * parkingFnCount r` parking functions of length `ℓ + r` whose letters
below `ℓ` are exactly at the positions of `S`. -/
theorem card_isParkingFn_lowSet (ℓ r : ℕ) (S : Finset (Fin (ℓ + r))) (hS : #S = ℓ) :
    #{z : Fin (ℓ + r) → Fin (ℓ + r) | IsParkingFn z ∧ ∀ k, ((z k : ℕ) < ℓ ↔ k ∈ S)} =
      parkingFnCount ℓ * parkingFnCount r := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff_lt ℓ r S hS
  rw [← card_isParkingFn_blocks]
  apply Finset.card_nbij' (fun z => z ∘ σ) (fun z => z ∘ σ.symm)
  · intro z hz
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hz ⊢
    refine ⟨(isParkingFn_comp_perm_iff z σ).2 hz.1, fun k => ?_⟩
    rw [Function.comp_apply, hz.2, hσ]
  · intro z hz
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hz ⊢
    refine ⟨(isParkingFn_comp_perm_iff z σ.symm).2 hz.1, fun k => ?_⟩
    rw [Function.comp_apply, hz.2, ← hσ, Equiv.apply_symm_apply]
  · intro z _
    funext k
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  · intro z _
    funext k
    simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- The breakpoint lemma: the parking functions of length `m` with exactly `ℓ` letters
smaller than `ℓ` number `(m choose ℓ) · P(ℓ) · P(m - ℓ)`, where `P(t) = parkingFnCount t`. -/
theorem breakpointCount_eq {m ℓ : ℕ} (h : ℓ ≤ m) :
    breakpointCount m ℓ = m.choose ℓ * parkingFnCount ℓ * parkingFnCount (m - ℓ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, breakpointCount,
    Finset.card_eq_sum_card_fiberwise (f := fun z => ({k | (z k : ℕ) < ℓ} : Finset _))
      (t := powersetCard ℓ univ) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => parkingFnCount ℓ * parkingFnCount r), sum_const,
      card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
    intro S hS
    rw [mem_powersetCard] at hS
    rw [← card_isParkingFn_lowSet ℓ r S hS.2, filter_filter]
    congr 1
    apply Finset.filter_congr
    intro z _
    constructor
    · rintro ⟨⟨hz, -⟩, hL⟩
      refine ⟨hz, fun k => ?_⟩
      rw [← hL, mem_filter]
      simp only [mem_univ, true_and]
    · rintro ⟨hz, hk⟩
      have hL : ({k | (z k : ℕ) < ℓ} : Finset _) = S := by
        ext k
        simp only [mem_filter, mem_univ, true_and, hk]
      exact ⟨⟨hz, by rw [hL, hS.2]⟩, hL⟩
  · intro z hz
    rw [mem_coe, mem_filter] at hz
    rw [mem_coe, mem_powersetCard]
    exact ⟨subset_univ _, hz.2.2⟩

end Parking

end
