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

public import Parking.CountPoly
public import Parking.External
public import Parking.WordLaw
public import Mathlib.Data.Nat.Choose.Multinomial
import Parking.Count
import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# The occupation polynomial of a uniform parking function

The source is the first assertion of `lem:occupation_logconcavity`. The occupation polynomial `G_n` of `π_n` is `countPoly (parkingWordLaw n)`.

* `countVector a` is the count vector `x = (x_1, …, x_n)` of a word `a`, with
  `x_j = occupation a j`.
* `parkingCountSet n` is the set `J` of count vectors of parking functions, described
  intrinsically: exponents of total degree `n` whose partial sums satisfy
  `x_0 + ⋯ + x_k ≥ k + 1` for every `k` (Lean values are 0-based).
* `isMConvex_parkingCountSet`: `J` is M-convex.
* `countPoly_parkingWordLaw`: `G_n = n! / (n + 1)^(n - 1) · f_J` (`lem:occupation_logconcavity`),
  using the count `n! / x!` of words with count vector `x` (`card_countVector_eq`).

The log-concavity consequences are proved in `Parking.Occupation`.
-/

public section

open MeasureTheory MvPolynomial Finset
open scoped Nat

namespace Parking

variable {n : ℕ+}

/-! ### Count vectors and the set `J` -/

/-- The count vector of a word `a`: its value at `j` is the number `occupation a j` of
coordinates whose preference is the mathematical value `j + 1`. -/
@[expose] noncomputable def countVector (a : Fin n → Fin n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (occupation a)

/-- The value of the count vector at `j` is the occupation count of `j`. -/
theorem countVector_apply (a : Fin n → Fin n) (j : Fin n) :
    countVector a j = occupation a j :=
  rfl

/-- The set `J` of count vectors of parking functions of size `n`, described intrinsically:
the exponents `x` of total degree `n` such that `x_0 + ⋯ + x_k ≥ k + 1` for every
`k : Fin n` (0-based Lean values; the source condition at `k + 1`). -/
@[expose] def parkingCountSet (n : ℕ+) : Finset (Fin n →₀ ℕ) :=
  (univ.finsuppAntidiag (n : ℕ)).filter fun x =>
    ∀ k : Fin n, k.val + 1 ≤ ∑ l ∈ Iic k, x l

/-- Membership in `J`: total degree `n` and the partial-sum condition. -/
theorem mem_parkingCountSet {x : Fin n →₀ ℕ} :
    x ∈ parkingCountSet n ↔
      ∑ l, x l = (n : ℕ) ∧ ∀ k : Fin n, k.val + 1 ≤ ∑ l ∈ Iic k, x l := by
  simp only [parkingCountSet, mem_filter, mem_finsuppAntidiag, subset_univ, and_true]

/-- The partial sum of the occupation counts up to `k` counts the preferences at most `k`. -/
theorem sum_Iic_occupation (a : Fin n → Fin n) (k : Fin n) :
    ∑ l ∈ Iic k, occupation a l = #{i | a i ≤ k} := by
  rw [card_eq_sum_card_fiberwise (f := a) (t := Iic k)
    (fun i hi => mem_Iic.2 (mem_filter.1 hi).2)]
  refine sum_congr rfl fun l hl => ?_
  unfold occupation
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro rfl
    exact ⟨mem_Iic.1 hl, rfl⟩
  · exact fun h => h.2

/-- A word is a parking function iff its count vector lies in `J`. -/
theorem isParkingFunction_iff_countVector_mem (a : Fin n → Fin n) :
    isParkingFunction a ↔ countVector a ∈ parkingCountSet n := by
  rw [mem_parkingCountSet]
  simp only [countVector_apply, sum_Iic_occupation, sum_occupation, true_and]
  rfl

/-- Every exponent in `J` has total degree `n`. -/
theorem degree_of_mem_parkingCountSet {x : Fin n →₀ ℕ} (hx : x ∈ parkingCountSet n) :
    x.degree = (n : ℕ) := by
  rw [Finsupp.degree_eq_sum]
  exact (mem_parkingCountSet.1 hx).1

/-- `J` is nonempty: it contains the count vector `(n, 0, …, 0)` of the all-ones parking
function. -/
theorem parkingCountSet_nonempty (n : ℕ+) : (parkingCountSet n).Nonempty :=
  ⟨_, (isParkingFunction_iff_countVector_mem _).1 (isParkingFunction_zero n)⟩

/-! ### M-convexity of `J` -/

/-- Adding a unit at `i` raises the total degree by one. -/
theorem sum_add_single_one (x : Fin n →₀ ℕ) (i : Fin n) :
    ∑ l, (x + Finsupp.single i 1 : Fin n →₀ ℕ) l = ∑ l, x l + 1 := by
  simp only [Finsupp.add_apply, sum_add_distrib, Finsupp.single_apply, sum_ite_eq, mem_univ,
    ↓reduceIte]

/-- Adding a unit at `i` raises the partial sum up to `k` by one exactly when `i ≤ k`. -/
theorem sum_Iic_add_single_one (x : Fin n →₀ ℕ) (i k : Fin n) :
    ∑ l ∈ Iic k, (x + Finsupp.single i 1 : Fin n →₀ ℕ) l =
      ∑ l ∈ Iic k, x l + if i ≤ k then 1 else 0 := by
  simp only [Finsupp.add_apply, sum_add_distrib, Finsupp.single_apply, sum_ite_eq, mem_Iic]

/-- `J` is M-convex. For `α, β ∈ J` with `α_i > β_i`, let `j` be the smallest index with
`α_j < β_j`. If `j < i`, moving a unit from `i` to `j` does not decrease any partial sum. If
`j > i`, then for `i ≤ k < j` the partial sum of `α` up to `k` exceeds that of `β`, hence is
at least `k + 2`, so removing a unit at `i` keeps the condition. -/
theorem isMConvex_parkingCountSet (n : ℕ+) :
    IsMConvex (parkingCountSet n : Set (Fin n →₀ ℕ)) := by
  intro α hα β hβ i hi
  rw [mem_coe, mem_parkingCountSet] at hα hβ
  obtain ⟨hαs, hαp⟩ := hα
  obtain ⟨hβs, hβp⟩ := hβ
  have hne : (univ.filter fun l => α l < β l).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
    have : ∑ l, β l < ∑ l, α l :=
      sum_lt_sum (fun l _ => not_lt.1 (h (mem_univ l))) ⟨i, mem_univ i, hi⟩
    omega
  obtain ⟨j, hj, hjmin⟩ : ∃ j, α j < β j ∧ ∀ l, α l < β l → j ≤ l :=
    ⟨_, (mem_filter.1 (min'_mem _ hne)).2,
      fun l hl => min'_le _ l (mem_filter.2 ⟨mem_univ l, hl⟩)⟩
  refine ⟨j, hj, ?_⟩
  have hle : Finsupp.single i 1 ≤ α := Finsupp.single_le_iff.2 (by omega)
  obtain ⟨α', rfl⟩ : ∃ α', α = α' + Finsupp.single i 1 :=
    ⟨α - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm⟩
  rw [add_tsub_cancel_right, mem_coe, mem_parkingCountSet]
  constructor
  · rw [sum_add_single_one]
    rw [sum_add_single_one] at hαs
    exact hαs
  · intro k
    have h1 := hαp k
    rw [sum_Iic_add_single_one] at h1
    rw [sum_Iic_add_single_one]
    by_cases hik : i ≤ k
    · by_cases hjk : j ≤ k
      · simp only [hik, hjk, ↓reduceIte] at h1 ⊢
        exact h1
      · have hlt : ∑ l ∈ Iic k, β l <
            ∑ l ∈ Iic k, (α' + Finsupp.single i 1 : Fin n →₀ ℕ) l := by
          refine sum_lt_sum (fun l hl => ?_) ⟨i, mem_Iic.2 hik, hi⟩
          by_contra h
          exact hjk ((hjmin l (not_le.1 h)).trans (mem_Iic.1 hl))
        have h2 := hβp k
        rw [sum_Iic_add_single_one] at hlt
        simp only [hik, hjk, ↓reduceIte, add_zero] at hlt ⊢
        omega
    · simp only [hik, ↓reduceIte, add_zero] at h1
      split_ifs <;> omega

/-! ### Words with a given count vector -/

/-- The count vector of `a` is `∑_i e_{a_i}`. -/
theorem countVector_eq_sum_single (a : Fin n → Fin n) :
    countVector a = ∑ i, Finsupp.single (a i) 1 := by
  ext j
  rw [countVector_apply, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, occupation, sum_boole, Nat.cast_id]

/-- The monomial `∏_i X_{a_i}` has exponent the count vector of `a`. -/
theorem prod_X_eq_monomial {R : Type*} [CommSemiring R] (a : Fin n → Fin n) :
    ∏ i, (X (a i) : MvPolynomial (Fin n) R) = monomial (countVector a) 1 := by
  rw [countVector_eq_sum_single, monomial_sum_one]
  rfl

/-- The coefficient of `x^m` in `∏_i X_{a_i}` is `1` if `m` is the count vector of `a`, and
`0` otherwise. -/
theorem coeff_prod_X {R : Type*} [CommSemiring R] (a : Fin n → Fin n) (m : Fin n →₀ ℕ) :
    (∏ i, (X (a i) : MvPolynomial (Fin n) R)).coeff m = if countVector a = m then 1 else 0 := by
  rw [prod_X_eq_monomial, coeff_monomial]

/-- The number of words with count vector `x` of total degree `n` is the multinomial
coefficient of `x`, by comparing coefficients in `(X_1 + ⋯ + X_n)^n`. -/
theorem card_countVector_eq_multinomial (x : Fin n →₀ ℕ) (hx : x.degree = (n : ℕ)) :
    #{a : Fin n → Fin n | countVector a = x} = Nat.multinomial univ x := by
  have h := coeff_sum_X_pow_of_fintype (R := ℕ) x (n : ℕ)
  rw [Fintype.sum_pow, coeff_sum] at h
  simp only [coeff_prod_X, sum_boole, Nat.cast_id] at h
  have hsum : x.sum (fun _ m => m) = (n : ℕ) := (Finsupp.degree_apply x).symm.trans hx
  simp only [hsum, ↓reduceIte] at h
  rw [h, Finsupp.multinomial_eq_of_support_subset (subset_univ _)]

/-- `#{a | countVector a = x} · x! = n!` for `x` of total degree `n`, with
`x! = ∏_j x_j!`. -/
theorem card_countVector_mul_prod_factorial (x : Fin n →₀ ℕ) (hx : x.degree = (n : ℕ)) :
    #{a : Fin n → Fin n | countVector a = x} * ∏ j, (x j)! = (n : ℕ)! := by
  rw [card_countVector_eq_multinomial x hx, mul_comm, Nat.multinomial_spec,
    ← Finsupp.degree_eq_sum, hx]

/-- A count vector `x` of total degree `n` has `n! / x!` orderings, with `x! = ∏_j x_j!`
(`lem:occupation_logconcavity`). -/
theorem card_countVector_eq (x : Fin n →₀ ℕ) (hx : x.degree = (n : ℕ)) :
    #{a : Fin n → Fin n | countVector a = x} = (n : ℕ)! / ∏ j, (x j)! := by
  rw [card_countVector_eq_multinomial x hx, Nat.multinomial, ← Finsupp.degree_eq_sum, hx]

/-! ### The normalisation `G_n = n! / (n + 1)^(n - 1) · f_J` -/

/-- The atoms of the law of `π_n` as a word: mass `1 / (n + 1)^(n - 1)` on parking
functions, `0` elsewhere. -/
theorem parkingWordLaw_real_singleton (n : ℕ+) (ω : Fin n → Fin n) :
    (parkingWordLaw n).real {ω} =
      if isParkingFunction ω then ((((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ) : ℝ)⁻¹ else 0 := by
  rw [parkingWordLaw, map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton ω),
    ProbabilityMeasure.measureReal_eq_coe_coeFn]
  have h : (fun a : ParkingFunction n => a.1) ⁻¹' {ω} =
      ↑(univ.filter fun a : ParkingFunction n => a.1 = ω) := by
    ext a
    simp
  rw [h, uniformParking, uniformLaw_apply, card_parkingFunction]
  split_ifs with hω
  · have hs : #(univ.filter fun a : ParkingFunction n => a.1 = ω) = 1 := by
      refine le_antisymm (card_le_one.2 fun a ha b hb => ?_)
        (card_pos.2 ⟨⟨ω, hω⟩, mem_filter.2 ⟨mem_univ _, rfl⟩⟩)
      rw [mem_filter] at ha hb
      exact Subtype.ext (ha.2.trans hb.2.symm)
    rw [hs, Nat.cast_one, one_div]
  · have hs : (univ.filter fun a : ParkingFunction n => a.1 = ω) = ∅ := by
      ext a
      simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
      rintro rfl
      exact hω a.2
    rw [hs, card_empty, Nat.cast_zero, zero_div]

/-- The coefficient of `x^m` in `G_n` is `#{a | countVector a = m} / (n + 1)^(n - 1)` if
`m ∈ J`, and `0` otherwise. -/
theorem coeff_countPoly_parkingWordLaw (n : ℕ+) (m : Fin n →₀ ℕ) :
    (countPoly (parkingWordLaw n)).coeff m =
      if m ∈ parkingCountSet n then
        (#{a : Fin n → Fin n | countVector a = m} : ℝ) *
          ((((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ) : ℝ)⁻¹
      else 0 := by
  rw [countPoly, coeff_sum]
  simp only [coeff_smul, coeff_prod_X, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  rw [sum_congr rfl (g := fun _ => if m ∈ parkingCountSet n then
    ((((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ) : ℝ)⁻¹ else 0) ?_]
  · rw [sum_const, nsmul_eq_mul]
    split_ifs <;> simp
  · intro ω hω
    rw [mem_filter] at hω
    rw [parkingWordLaw_real_singleton]
    exact if_congr ((isParkingFunction_iff_countVector_mem ω).trans (by rw [hω.2])) rfl rfl

/-- The coefficient of `x^m` in `f_J` is `1 / m!` if `m ∈ J`, and `0` otherwise. -/
theorem coeff_supportGenFun {d : ℕ} (J : Finset (Fin d →₀ ℕ)) (m : Fin d →₀ ℕ) :
    (supportGenFun J).coeff m = if m ∈ J then (∏ i, ((m i)! : ℝ))⁻¹ else 0 := by
  rw [supportGenFun, coeff_sum]
  simp only [coeff_monomial]
  rw [sum_ite_eq']

/-- `G_n = n! / (n + 1)^(n - 1) · f_J` (`lem:occupation_logconcavity`): a parking function with
count vector `x` has probability `1 / (n + 1)^(n - 1)`, and `x` has `n! / x!` orderings. -/
theorem countPoly_parkingWordLaw (n : ℕ+) :
    countPoly (parkingWordLaw n) =
      (((n : ℕ).factorial : ℝ) / (((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ)) •
        supportGenFun (parkingCountSet n) := by
  ext m
  rw [coeff_countPoly_parkingWordLaw, coeff_smul, coeff_supportGenFun, smul_eq_mul]
  split_ifs with hm
  · have h := card_countVector_mul_prod_factorial m (degree_of_mem_parkingCountSet hm)
    have hR : (#{a : Fin n → Fin n | countVector a = m} : ℝ) * ∏ j, ((m j)! : ℝ) =
        ((n : ℕ)! : ℝ) := by
      exact_mod_cast h
    have hP : (∏ j, ((m j)! : ℝ)) ≠ 0 :=
      prod_ne_zero_iff.2 fun j _ => by positivity
    have hC : ((((n : ℕ) + 1) ^ ((n : ℕ) - 1) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [← hR]
    field_simp
  · rw [mul_zero]

end Parking

end
