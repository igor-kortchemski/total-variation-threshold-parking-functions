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

public import Parking.Law

/-!
# The number of parking functions

The source is the introductory definitions: `|PF_n| = (n + 1)^(n - 1)` [KW66].
The proof is Pollak's circular argument, phrased as a cycle lemma on counts.

Put `N + 1` spots on a circle and let `w : Fin N → Fin (N + 1)` be any word. Let
`a_k` be the number of letters of `w` equal to `k` modulo `N + 1`, and let
`S(t) = ∑_{k < t} (a_k - 1)`. Since the `a_k` sum to `N` over a period,
`S(t + N + 1) = S(t) - 1`. The word `i ↦ w i - c` is a parking function, read in
`Fin N`, exactly when `S(c) ≤ S(c + t)` for `1 ≤ t ≤ N`, and exactly one
`c : Fin (N + 1)` has this property (`existsUnique_cyclicStart`). Hence
`(a, c) ↦ (i ↦ a i + c)` is a bijection from `ParkingFunction n × Fin (n + 1)` onto
`Fin n → Fin (n + 1)`, and `|PF_n| · (n + 1) = (n + 1)^n`.
-/

public section

namespace Parking

open Finset

/-- Two distinct starts in a period cannot both keep the walk above its starting value. -/
theorem cyclicStart_unique_aux {m : ℕ} {S : ℕ → ℤ} (hS : ∀ t, S (t + m) = S t - 1)
    {c c' : ℕ} (hc : ∀ t, 1 ≤ t → t < m → S c ≤ S (c + t))
    (hc' : ∀ t, 1 ≤ t → t < m → S c' ≤ S (c' + t)) (hlt : c < c') (hc'm : c' < m) :
    False := by
  have h1 := hc (c' - c) (by omega) (by omega)
  rw [show c + (c' - c) = c' by omega] at h1
  have h2 := hc' (c + m - c') (by omega) (by omega)
  rw [show c' + (c + m - c') = c + m by omega, hS] at h2
  linarith

/-- Cycle lemma: if an integer walk loses one unit over every period of length `m`,
exactly one start in a period keeps the walk at or above its starting value during the
following `m - 1` steps. -/
theorem existsUnique_cyclicStart (m : ℕ) [NeZero m] (S : ℕ → ℤ)
    (hS : ∀ t, S (t + m) = S t - 1) :
    ∃! c : Fin m, ∀ t, 1 ≤ t → t < m → S c ≤ S ((c : ℕ) + t) := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  -- The value `m * S c + c` is injective on a period; its minimum is the unique start.
  obtain ⟨c, -, hc⟩ := Finset.exists_min_image Finset.univ
    (fun c : Fin m => (m : ℤ) * S c + c) Finset.univ_nonempty
  have hgood : ∀ t, 1 ≤ t → t < m → S c ≤ S ((c : ℕ) + t) := by
    intro t ht1 htm
    by_cases hlt : (c : ℕ) + t < m
    · have key := hc ⟨c + t, hlt⟩ (Finset.mem_univ _)
      simp only [Nat.cast_add] at key
      by_contra h
      have h1 : S (c + t) + 1 ≤ S c := by omega
      have h2 : (m : ℤ) * (S (c + t) + 1) ≤ m * S c :=
        mul_le_mul_of_nonneg_left h1 hm.le
      have h3 : (t : ℤ) < m := by exact_mod_cast htm
      linarith
    · have hs : (c : ℕ) + t - m < m := by omega
      have key := hc ⟨c + t - m, hs⟩ (Finset.mem_univ _)
      simp only at key
      have hcast : (((c : ℕ) + t - m : ℕ) : ℤ) < (c : ℕ) := by omega
      rw [show (c : ℕ) + t = (c + t - m) + m by omega, hS]
      by_contra h
      have h1 : S (c + t - m) ≤ S c := by omega
      have h2 : (m : ℤ) * S (c + t - m) ≤ m * S c :=
        mul_le_mul_of_nonneg_left h1 hm.le
      linarith
  refine ⟨c, hgood, fun c' hc' => ?_⟩
  rcases lt_trichotomy (c' : ℕ) c with h | h | h
  · exact (cyclicStart_unique_aux hS hc' hgood h c.isLt).elim
  · exact Fin.ext h
  · exact (cyclicStart_unique_aux hS hgood hc' h c'.isLt).elim

variable {N : ℕ}

/-- The number `a_k` of letters of `w` equal to `k` modulo `N + 1`. -/
@[expose] def cyclicLetterCount (w : Fin N → Fin (N + 1)) (k : ℕ) : ℕ :=
  #{i | (w i : ℕ) = k % (N + 1)}

/-- The walk `S(t) = ∑_{k < t} (a_k - 1)`, where `a_k = cyclicLetterCount w k`. -/
@[expose] def cyclicWalk (w : Fin N → Fin (N + 1)) (t : ℕ) : ℤ :=
  ∑ k ∈ range t, ((cyclicLetterCount w k : ℤ) - 1)

/-- A word with letters in `Fin (N + 1)` is a parking word if, for every `1 ≤ t ≤ N`,
at least `t` of its letters are smaller than `t`. -/
@[expose] def IsParkingWord (u : Fin N → Fin (N + 1)) : Prop :=
  ∀ t, 1 ≤ t → t ≤ N → t ≤ #{i | (u i : ℕ) < t}

/-- Letters of the shifted word `w - c` equal to `k` are letters of `w` equal to `c + k`. -/
theorem card_sub_val_eq (w : Fin N → Fin (N + 1)) (c : Fin (N + 1)) {k : ℕ}
    (hk : k < N + 1) :
    #{i | ((w i - c : Fin (N + 1)) : ℕ) = k} = cyclicLetterCount w ((c : ℕ) + k) := by
  unfold cyclicLetterCount
  congr 1
  apply Finset.filter_congr
  intro i _
  have h : ((w i - c : Fin (N + 1)) : ℕ) = k ↔ w i - c = ⟨k, hk⟩ :=
    ⟨fun h' => Fin.ext h', fun h' => congrArg Fin.val h'⟩
  rw [h, sub_eq_iff_eq_add, Fin.ext_iff, Fin.val_add, Nat.add_comm k]

/-- The number of letters of `w - c` below `t` is `∑_{k < t} a_{c + k}`. -/
theorem card_sub_val_lt (w : Fin N → Fin (N + 1)) (c : Fin (N + 1)) {t : ℕ}
    (ht : t ≤ N + 1) :
    #{i | ((w i - c : Fin (N + 1)) : ℕ) < t} =
      ∑ k ∈ range t, cyclicLetterCount w ((c : ℕ) + k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih (by omega), ← card_sub_val_eq w c (by omega : t < N + 1),
      ← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    · rw [Finset.disjoint_filter]
      intro i _ h1 h2
      omega

/-- The increments of the walk after `c` count the letters of `w - c`. -/
theorem sum_cyclicIncrement (w : Fin N → Fin (N + 1)) (c : Fin (N + 1)) {t : ℕ}
    (ht : t ≤ N + 1) :
    ∑ k ∈ range t, ((cyclicLetterCount w ((c : ℕ) + k) : ℤ) - 1) =
      (#{i | ((w i - c : Fin (N + 1)) : ℕ) < t} : ℤ) - t := by
  rw [Finset.sum_sub_distrib, card_sub_val_lt w c ht]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_sum]

theorem cyclicWalk_add (w : Fin N → Fin (N + 1)) (c : Fin (N + 1)) {t : ℕ}
    (ht : t ≤ N + 1) :
    cyclicWalk w ((c : ℕ) + t) =
      cyclicWalk w c + #{i | ((w i - c : Fin (N + 1)) : ℕ) < t} - t := by
  unfold cyclicWalk
  rw [Finset.sum_range_add, sum_cyclicIncrement w c ht]
  ring

/-- The walk loses one unit over every period, since `w` has `N` letters. -/
theorem cyclicWalk_add_period (w : Fin N → Fin (N + 1)) (t : ℕ) :
    cyclicWalk w (t + (N + 1)) = cyclicWalk w t - 1 := by
  let c : Fin (N + 1) := ⟨t % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩
  have hct : ∀ k : ℕ, cyclicLetterCount w (t + k) = cyclicLetterCount w ((c : ℕ) + k) := by
    intro k
    unfold cyclicLetterCount
    rw [Nat.mod_add_mod]
  have hall : #{i | ((w i - c : Fin (N + 1)) : ℕ) < N + 1} = N := by
    rw [Finset.filter_true_of_mem (fun i _ => (w i - c).isLt), Finset.card_univ,
      Fintype.card_fin]
  unfold cyclicWalk
  rw [Finset.sum_range_add]
  simp_rw [hct]
  rw [sum_cyclicIncrement w c le_rfl, hall]
  push_cast
  ring

/-- The shifted word `w - c` is a parking word iff the walk started at `c` stays at or
above its starting value during `N` steps. -/
theorem isParkingWord_sub_iff (w : Fin N → Fin (N + 1)) (c : Fin (N + 1)) :
    IsParkingWord (fun i => w i - c) ↔
      ∀ t, 1 ≤ t → t < N + 1 → cyclicWalk w c ≤ cyclicWalk w ((c : ℕ) + t) := by
  apply forall_congr'
  intro t
  constructor
  · intro h h1 h2
    rw [cyclicWalk_add w c (by omega)]
    have h3 : (t : ℤ) ≤ (#{i | ((w i - c : Fin (N + 1)) : ℕ) < t} : ℕ) := by
      exact_mod_cast h h1 (by omega)
    linarith
  · intro h h1 h2
    have h3 := h h1 (by omega)
    rw [cyclicWalk_add w c (by omega)] at h3
    have h4 : (t : ℤ) ≤ (#{i | ((w i - c : Fin (N + 1)) : ℕ) < t} : ℕ) := by linarith
    exact_mod_cast h4

/-- Pollak's cycle lemma: every word has exactly one cyclic shift that is a parking
word. -/
theorem existsUnique_isParkingWord_sub (w : Fin N → Fin (N + 1)) :
    ∃! c : Fin (N + 1), IsParkingWord (fun i => w i - c) := by
  obtain ⟨c, hc, huniq⟩ :=
    existsUnique_cyclicStart (N + 1) (cyclicWalk w) (cyclicWalk_add_period w)
  exact ⟨c, (isParkingWord_sub_iff w c).2 hc,
    fun c' h => huniq c' ((isParkingWord_sub_iff w c').1 h)⟩

/-- A parking word never uses the letter `N`. -/
theorem IsParkingWord.ne_last {u : Fin N → Fin (N + 1)} (hu : IsParkingWord u) (i : Fin N) :
    u i ≠ Fin.last N := by
  have hN : 1 ≤ N := by have := i.isLt; omega
  have h := hu N hN le_rfl
  have hle : #{j | (u j : ℕ) < N} ≤ N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun j => (u j : ℕ) < N)
  have hall := Finset.filter_card_eq (s := (Finset.univ : Finset (Fin N)))
    (p := fun j => (u j : ℕ) < N) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    i (Finset.mem_univ i)
  intro hi
  rw [hi, Fin.val_last] at hall
  exact lt_irrefl _ hall

theorem card_castSucc_lt {n : ℕ+} (a : Fin n → Fin n) (j : Fin n) :
    #{i | ((Fin.castSucc (a i) : Fin ((n : ℕ) + 1)) : ℕ) < j + 1} = #{i | a i ≤ j} := by
  congr 1

/-- Parking functions are the parking words that avoid the letter `n`. -/
theorem isParkingFunction_iff_isParkingWord {n : ℕ+} (a : Fin n → Fin n) :
    isParkingFunction a ↔ IsParkingWord (fun i => Fin.castSucc (a i)) := by
  constructor
  · intro h t h1 h2
    obtain ⟨j, rfl⟩ : ∃ j : Fin n, t = j + 1 := ⟨⟨t - 1, by omega⟩, by simp only; omega⟩
    rw [card_castSucc_lt]
    exact h j
  · intro h j
    rw [← card_castSucc_lt]
    exact h (j + 1) (by omega) j.isLt

/-- Pollak's bijection: `|PF_n| · (n + 1) = (n + 1)^n`. -/
theorem card_parkingFunction_mul (n : ℕ+) :
    Fintype.card (ParkingFunction n) * ((n : ℕ) + 1) = ((n : ℕ) + 1) ^ (n : ℕ) := by
  let f : ParkingFunction n × Fin ((n : ℕ) + 1) → (Fin n → Fin ((n : ℕ) + 1)) :=
    fun p i => Fin.castSucc (p.1.1 i) + p.2
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, c⟩ ⟨a', c'⟩ h
      have h1 : IsParkingWord (fun i => f (a, c) i - c) := by
        simp only [f, add_sub_cancel_right]
        exact (isParkingFunction_iff_isParkingWord a.1).1 a.2
      have h2 : IsParkingWord (fun i => f (a, c) i - c') := by
        rw [h]
        simp only [f, add_sub_cancel_right]
        exact (isParkingFunction_iff_isParkingWord a'.1).1 a'.2
      obtain rfl : c = c' := (existsUnique_isParkingWord_sub (f (a, c))).unique h1 h2
      obtain rfl : a = a' := by
        apply Subtype.ext
        funext i
        have hi := congrFun h i
        simp only [f, add_left_inj] at hi
        exact Fin.castSucc_injective _ hi
      rfl
    · intro w
      obtain ⟨c, hc, -⟩ := existsUnique_isParkingWord_sub w
      refine ⟨(⟨fun i => (w i - c).castPred (hc.ne_last i), ?_⟩, c), ?_⟩
      · rw [isParkingFunction_iff_isParkingWord]
        simpa only [Fin.castSucc_castPred] using hc
      · funext i
        simp only [f, Fin.castSucc_castPred, sub_add_cancel]
  rw [← Fintype.card_fin ((n : ℕ) + 1), ← Fintype.card_prod, Fintype.card_of_bijective hf,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Konheim–Weiss: there are `(n + 1)^(n - 1)` parking functions of size `n`
(the introductory definitions). -/
theorem card_parkingFunction (n : ℕ+) :
    Fintype.card (ParkingFunction n) = ((n : ℕ) + 1) ^ ((n : ℕ) - 1) := by
  have h := card_parkingFunction_mul n
  have h2 : ((n : ℕ) + 1) ^ (n : ℕ) = ((n : ℕ) + 1) ^ ((n : ℕ) - 1) * ((n : ℕ) + 1) := by
    rw [← pow_succ, Nat.sub_add_cancel n.pos]
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) h

end Parking

end
