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

public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Parking functions and occupation counts

The source is `parking_threshold.tex`, lines 64–76 and 172–178.
The size `n : ℕ+` is positive. A word `a : Fin n → Fin n` represents
the mathematical preferences `a i + 1`, indexed by `i + 1`.
Thus the source condition at `j + 1` is the count of coordinates with
`a i ≤ j`. The constant zero word represents the all-ones parking function.

This module establishes only finite combinatorial foundations. It does not
assert the enumeration formula, probability estimates, or limit theorems.
-/

public section

namespace Parking

open scoped BigOperators

/-- A word is a parking function if at least `j + 1` preferences are at most
`j + 1`, with both coordinates and preferences represented by `Fin n`. -/
@[expose] def isParkingFunction {n : ℕ+} (a : Fin n → Fin n) : Prop :=
  ∀ j : Fin n, j.val + 1 ≤ (Finset.univ.filter (fun i => a i ≤ j)).card

/-- Parking functions of positive size `n`, as the subtype of admissible words. -/
@[expose] def ParkingFunction (n : ℕ+) :=
  {a : Fin n → Fin n // isParkingFunction a}

/-- The number of coordinates whose preference equals the mathematical value `j + 1`. -/
@[expose] def occupation {n : ℕ+} (a : Fin n → Fin n) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => a i = j)).card

variable {n : ℕ+}

/-- Permuting coordinates preserves every lower-level count. -/
theorem count_le_comp_perm (a : Fin n → Fin n) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    (Finset.univ.filter (fun i => (a ∘ σ) i ≤ j)).card =
      (Finset.univ.filter (fun i => a i ≤ j)).card := by
  apply Finset.card_equiv σ
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]

/-- Admissibility is invariant under every permutation of coordinates. -/
theorem isParkingFunction_comp_perm_iff (a : Fin n → Fin n)
    (σ : Equiv.Perm (Fin n)) :
    isParkingFunction (a ∘ σ) ↔ isParkingFunction a := by
  simp only [isParkingFunction, count_le_comp_perm]

/-- Every occupation count is invariant under a permutation of coordinates. -/
theorem occupation_comp_perm (a : Fin n → Fin n) (σ : Equiv.Perm (Fin n))
    (j : Fin n) : occupation (a ∘ σ) j = occupation a j := by
  unfold occupation
  apply Finset.card_equiv σ
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]

/-- The word representing preference one at every coordinate is a parking function. -/
theorem isParkingFunction_zero (n : ℕ+) :
    isParkingFunction (fun _ : Fin n => (0 : Fin n)) := by
  intro j
  change j.val + 1 ≤ (Finset.univ.filter (fun _ : Fin n => (0 : Fin n) ≤ j)).card
  rw [Finset.filter_eq_self.mpr (fun _ _ => Fin.zero_le j), Finset.card_fin]
  exact Nat.succ_le_of_lt j.isLt

/-- There is a parking function for every positive size. -/
theorem parkingFunction_nonempty (n : ℕ+) : Nonempty (ParkingFunction n) :=
  ⟨⟨fun _ => 0, isParkingFunction_zero n⟩⟩

/-- The occupation counts of any word sum to its length. -/
theorem sum_occupation (a : Fin n → Fin n) :
    ∑ j : Fin n, occupation a j = (n : ℕ) := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := a) (s := Finset.univ) (t := Finset.univ)
    (fun i _ => Finset.mem_univ (a i))
  simpa only [occupation, Finset.card_fin] using h.symm

end Parking

end
