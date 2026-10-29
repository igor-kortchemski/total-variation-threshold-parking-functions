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

public import Parking.OccupationCounting
public import Parking.Paper.LinearSubstitution
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The prefix-linear product and its support

The product in `lem:occupation_logconcavity`, with the source's
ordering argument. The sorted-order characterization also supplies the
introductory characterization of parking functions. No log-concavity claim is
assumed in the support calculation.
-/

@[expose] public section

open MvPolynomial Finset

namespace Parking

variable {n : ℕ+}

/-- The factor `z₁ + ⋯ + zᵢ` of the manuscript, with zero-based indices. -/
noncomputable def prefixLinearForm (n : ℕ+) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ Iic i, X j

/-- The product of the prefix linear forms, in `lem:occupation_logconcavity`. -/
noncomputable def prefixLinearProduct (n : ℕ+) : MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin n, prefixLinearForm n i

/-- Choosing from factor `i` gives a parking function because its first `j+1`
choices are all at most `j`. -/
theorem isParkingFunction_of_le_index (a : Fin n → Fin n) (ha : ∀ i, a i ≤ i) :
    isParkingFunction a := by
  intro j
  have hs : Iic j ⊆ univ.filter (fun i => a i ≤ j) := by
    intro i hi
    exact mem_filter.2 ⟨mem_univ _, (ha i).trans (mem_Iic.1 hi)⟩
  simpa only [Fin.card_Iic] using card_le_card hs

/-- The nondecreasing rearrangement of a parking function satisfies `aᵢ ≤ i`. -/
theorem isParkingFunction_iff_sort_le (a : Fin n → Fin n) :
    isParkingFunction a ↔ ∀ i, a (Tuple.sort a i) ≤ i := by
  constructor
  · intro ha i
    have hp := (isParkingFunction_comp_perm_iff a (Tuple.sort a)).2 ha i
    exact (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort a)).1
      (Nat.lt_of_succ_le hp)
  · intro ha
    exact (isParkingFunction_comp_perm_iff a (Tuple.sort a)).1
      (isParkingFunction_of_le_index (a ∘ Tuple.sort a) ha)

/-- Permutations preserve the complete occupation vector. -/
theorem countVector_comp_perm (a : Fin n → Fin n) (σ : Equiv.Perm (Fin n)) :
    countVector (a ∘ σ) = countVector a := by
  ext j
  exact occupation_comp_perm a σ j

/-- Every nonnegative occupation vector of total size `n` has a word realizing it. -/
theorem exists_countVector_eq (x : Fin n →₀ ℕ) (hx : x.degree = (n : ℕ)) :
    ∃ a : Fin n → Fin n, countVector a = x := by
  have hpos : 0 < #{a : Fin n → Fin n | countVector a = x} := by
    rw [card_countVector_eq_multinomial x hx]
    exact Nat.multinomial_pos _ _
  obtain ⟨a, ha⟩ := card_pos.1 hpos
  exact ⟨a, (mem_filter.1 ha).2⟩

/-- The support described intrinsically by parking counts has an ordered choice
of one variable from every prefix factor. -/
theorem mem_parkingCountSet_iff_exists_le_index (x : Fin n →₀ ℕ) :
    x ∈ parkingCountSet n ↔
      ∃ a : Fin n → Fin n, (∀ i, a i ≤ i) ∧ countVector a = x := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := exists_countVector_eq x (degree_of_mem_parkingCountSet hx)
    have hp : isParkingFunction a := (isParkingFunction_iff_countVector_mem a).2 (ha ▸ hx)
    exact ⟨a ∘ Tuple.sort a, (isParkingFunction_iff_sort_le a).1 hp,
      (countVector_comp_perm a _).trans ha⟩
  · rintro ⟨a, ha, rfl⟩
    exact (isParkingFunction_iff_countVector_mem a).1 (isParkingFunction_of_le_index a ha)

/-- Expanding the prefix product sums one monomial for each permitted sequence
of choices, before equal monomials are collected. -/
theorem prefixLinearProduct_eq_sum (n : ℕ+) :
    prefixLinearProduct n = ∑ a ∈ Fintype.piFinset (fun i : Fin n => Iic i),
      ∏ i, (X (a i) : MvPolynomial (Fin n) ℝ) := by
  exact Finset.prod_univ_sum (fun i : Fin n => Iic i) (fun _ j => X j)

/-- The coefficient of a monomial in the prefix product counts precisely the
ordered choices that have its occupation vector. -/
theorem coeff_prefixLinearProduct (n : ℕ+) (x : Fin n →₀ ℕ) :
    (prefixLinearProduct n).coeff x =
      ((Fintype.piFinset (fun i : Fin n => Iic i)).filter
        (fun a => countVector a = x)).card := by
  rw [prefixLinearProduct_eq_sum, coeff_sum]
  simp only [coeff_prod_X, sum_boole]

/-- Manuscript `lem:occupation_logconcavity`: the prefix product has exactly the parking
occupation vectors as its support, by choosing and sorting words. -/
theorem support_prefixLinearProduct (n : ℕ+) :
    (prefixLinearProduct n).support = parkingCountSet n := by
  ext x
  rw [mem_support_iff, coeff_prefixLinearProduct, Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero,
    card_pos, mem_parkingCountSet_iff_exists_le_index]
  simp only [Finset.Nonempty, mem_filter, Fintype.mem_piFinset, mem_Iic]

/-- The source prefix product is strongly log-concave by the proved closure
specialization for products of nonnegative linear forms. -/
theorem stronglyLogConcave_prefixLinearProduct (n : ℕ+) :
    StronglyLogConcave (prefixLinearProduct n) := by
  let A : Fin n → Fin n → ℝ := fun i j => if j ≤ i then 1 else 0
  have hA : ∀ i j, 0 ≤ A i j := by intro i j; simp only [A]; split_ifs <;> positivity
  have hrow : ∀ i, ∃ j, 0 < A i j := fun i => ⟨i, by simp [A]⟩
  have h := stronglyLogConcave_prod_nonnegativeLinearForm A hA hrow
  have hform (i : Fin n) : nonnegativeLinearForm (A i) = prefixLinearForm n i := by
    simp only [nonnegativeLinearForm, A, ite_smul, one_smul, zero_smul,
      prefixLinearForm]
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  simpa only [hform, prefixLinearProduct] using h

end Parking

end
