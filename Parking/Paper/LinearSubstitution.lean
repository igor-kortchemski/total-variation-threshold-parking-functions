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

public import Parking.SupportGenFunCLC
public import Parking.CLCCriterion
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Products of nonnegative linear forms

A specialization of the product-closure result [BH20, Corollary 2.32] used in
`lem:occupation_logconcavity`. A monomial is completely log-concave, and substitution
of nonnegative linear forms preserves complete log-concavity. The definitions
of strong and complete log-concavity remain the independent analytic definitions
in `Parking.LogConcave`.
-/

@[expose] public section

open MvPolynomial Finset

namespace Parking

/-- The linear form with coefficients `a`. -/
noncomputable def nonnegativeLinearForm {d : ℕ} (a : Fin d → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ j, a j • X j

/-- The linear map on evaluation points associated with a matrix of coefficients. -/
noncomputable def substitutionLinearMap {m d : ℕ} (A : Fin m → Fin d → ℝ) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun z i := ∑ j, A i j * z j
  map_add' x y := by
    ext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Substitute the row linear forms of `A` into a polynomial. -/
noncomputable def linearSubstitution {m d : ℕ} (A : Fin m → Fin d → ℝ) :
    MvPolynomial (Fin m) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  aeval (fun i => nonnegativeLinearForm (A i))

theorem eval_nonnegativeLinearForm {d : ℕ} (a z : Fin d → ℝ) :
    eval z (nonnegativeLinearForm a) = ∑ j, a j * z j := by
  simp [nonnegativeLinearForm, smul_eval]

theorem eval_linearSubstitution {m d : ℕ} (A : Fin m → Fin d → ℝ)
    (f : MvPolynomial (Fin m) ℝ) (z : Fin d → ℝ) :
    eval z (linearSubstitution A f) = eval (substitutionLinearMap A z) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [linearSubstitution]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_mul, eval_X]
    rw [linearSubstitution, aeval_X, eval_nonnegativeLinearForm]
    rfl

theorem coeff_mul_nonneg {d : ℕ} {f g : MvPolynomial (Fin d) ℝ}
    (hf : ∀ α, 0 ≤ f.coeff α) (hg : ∀ α, 0 ≤ g.coeff α) (α : Fin d →₀ ℕ) :
    0 ≤ (f * g).coeff α := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf x.1) (hg x.2)

theorem coeff_pow_nonneg {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : ∀ α, 0 ≤ f.coeff α) (r : ℕ) (α : Fin d →₀ ℕ) :
    0 ≤ (f ^ r).coeff α := by
  induction r generalizing α with
  | zero => simp only [pow_zero, coeff_one]; split_ifs <;> positivity
  | succ r ih =>
    rw [pow_succ]
    exact coeff_mul_nonneg ih hf α

theorem coeff_finset_prod_nonneg {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) ℝ) (hf : ∀ i ∈ s, ∀ α, 0 ≤ (f i).coeff α)
    (α : Fin d →₀ ℕ) : 0 ≤ (∏ i ∈ s, f i).coeff α := by
  classical
  induction s using Finset.induction_on generalizing α with
  | empty => simp only [Finset.prod_empty, coeff_one]; split_ifs <;> positivity
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact coeff_mul_nonneg (hf i (by simp)) (fun β => ih (fun j hj => hf j (by simp [hj])) β) α

theorem coeff_aeval_nonneg {m d : ℕ} (g : Fin m → MvPolynomial (Fin d) ℝ)
    (hg : ∀ i α, 0 ≤ (g i).coeff α) {f : MvPolynomial (Fin m) ℝ}
    (hf : ∀ α, 0 ≤ f.coeff α) (α : Fin d →₀ ℕ) : 0 ≤ (aeval g f).coeff α := by
  conv_rhs => rw [f.as_sum]
  rw [map_sum, coeff_sum]
  refine Finset.sum_nonneg fun β _ => ?_
  rw [aeval_monomial]
  change 0 ≤ (C (f.coeff β) * ∏ i ∈ β.support, g i ^ β i).coeff α
  rw [coeff_C_mul]
  exact mul_nonneg (hf β)
    (coeff_finset_prod_nonneg β.support _ (fun i _ => coeff_pow_nonneg (hg i) _) α)

theorem coeff_nonnegativeLinearForm_nonneg {d : ℕ} {a : Fin d → ℝ}
    (ha : ∀ i, 0 ≤ a i) (α : Fin d →₀ ℕ) :
    0 ≤ (nonnegativeLinearForm a).coeff α := by
  rw [nonnegativeLinearForm, coeff_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [coeff_smul, smul_eq_mul, coeff_X]
  exact mul_nonneg (ha i) (by split_ifs <;> positivity)

theorem dirDeriv_mul {d : ℕ} (v : Fin d → ℝ) (f g : MvPolynomial (Fin d) ℝ) :
    dirDeriv v (f * g) = dirDeriv v f * g + f * dirDeriv v g := by
  simp only [dirDeriv_apply, pderiv_mul, smul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

theorem dirDeriv_X {d : ℕ} (v : Fin d → ℝ) (i : Fin d) :
    dirDeriv v (X i) = C (v i) := by
  rw [dirDeriv_apply, Finset.sum_eq_single i]
  · simp [smul_eq_C_mul]
  · intro j _ hj
    simp [pderiv_X_of_ne (Ne.symm hj)]
  · simp

theorem dirDeriv_nonnegativeLinearForm {d : ℕ} (a v : Fin d → ℝ) :
    dirDeriv v (nonnegativeLinearForm a) = C (∑ i, a i * v i) := by
  rw [nonnegativeLinearForm, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.map_smul, dirDeriv_X, smul_eq_C_mul, ← map_mul]

/-- The polynomial chain rule for substitution by linear forms. -/
theorem dirDeriv_linearSubstitution {m d : ℕ} (A : Fin m → Fin d → ℝ)
    (f : MvPolynomial (Fin m) ℝ) (v : Fin d → ℝ) :
    dirDeriv v (linearSubstitution A f) =
      linearSubstitution A (dirDeriv (substitutionLinearMap A v) f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [linearSubstitution, dirDeriv_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, dirDeriv_mul, map_add, hp, dirDeriv_X]
    simp only [linearSubstitution, aeval_X, aeval_C, algebraMap_eq,
      dirDeriv_nonnegativeLinearForm]
    rfl

/-- Iterating the chain rule transforms every direction by the same linear map. -/
theorem prod_dirDeriv_linearSubstitution {m d : ℕ} (A : Fin m → Fin d → ℝ)
    (f : MvPolynomial (Fin m) ℝ) (vs : List (Fin d → ℝ)) :
    (vs.map dirDeriv).prod (linearSubstitution A f) =
      linearSubstitution A
        (((vs.map (substitutionLinearMap A)).map dirDeriv).prod f) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih,
      dirDeriv_linearSubstitution]

/-- A nonnegative matrix with a positive entry in every row maps the positive
orthant into the positive orthant. -/
theorem substitutionLinearMap_pos {m d : ℕ} {A : Fin m → Fin d → ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    {z : Fin d → ℝ} (hz : z ∈ posOrthant d) :
    substitutionLinearMap A z ∈ posOrthant m := by
  intro i
  obtain ⟨j, hj⟩ := hrow i
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hA i k) (hz k).le)
    ⟨j, Finset.mem_univ _, mul_pos hj (hz j)⟩

/-- Nonnegative linear substitution preserves complete log-concavity when each
substituted form is nonzero. This version suffices for every prefix form. -/
theorem CompletelyLogConcave.linearSubstitution {m d : ℕ} {f : MvPolynomial (Fin m) ℝ}
    (hf : CompletelyLogConcave f) (A : Fin m → Fin d → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j) :
    CompletelyLogConcave (linearSubstitution A f) := by
  refine ⟨coeff_aeval_nonneg _ (fun i => coeff_nonnegativeLinearForm_nonneg (hA i)) hf.1,
    fun vs hvs => ?_⟩
  rw [prod_dirDeriv_linearSubstitution]
  have hvA : ∀ v ∈ vs.map (substitutionLinearMap A), ∀ i, 0 ≤ v i := by
    intro v hv i
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    change 0 ≤ ∑ j, A i j * w j
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hvs w hw j)
  rcases hf.2 _ hvA with hzero | hconc
  · left
    rw [hzero, map_zero]
  · right
    have h := (hconc.comp_linearMap (substitutionLinearMap A)).subset
      (fun z hz => substitutionLinearMap_pos hA hrow hz) (convex_posOrthant d)
    simpa only [Function.comp_def, eval_linearSubstitution] using h

/-- The product of distinct variables is completely log-concave. Here the
existing proved support-normalization theorem is used only on a singleton. -/
theorem completelyLogConcave_prod_X (m : ℕ) :
    CompletelyLogConcave (∏ i : Fin m, (X i : MvPolynomial (Fin m) ℝ)) := by
  let α : Fin m →₀ ℕ := ∑ i : Fin m, Finsupp.single i 1
  have hα (i : Fin m) : α i = 1 := by simp [α]
  have hdeg : α.degree = m := by rw [Finsupp.degree_eq_sum]; simp [hα]
  have hM : IsMConvex ({α} : Set (Fin m →₀ ℕ)) := by
    intro β hβ γ hγ i hi
    rw [Set.mem_singleton_iff.mp hβ, Set.mem_singleton_iff.mp hγ] at hi
    exact False.elim (lt_irrefl _ hi)
  have h := bh20_supportGenFunCLC m m {α} (Finset.singleton_nonempty _)
    (fun β hβ => by rwa [Finset.mem_singleton.mp hβ])
    (by simpa only [Finset.coe_singleton] using hM)
  have heq : supportGenFun {α} = ∏ i : Fin m, (X i : MvPolynomial (Fin m) ℝ) := by
    simp only [supportGenFun, Finset.sum_singleton, hα, Nat.factorial_one, Nat.cast_one,
      Finset.prod_const_one, inv_one]
    rw [show α = ∑ i : Fin m, Finsupp.single i 1 from rfl, monomial_sum_one]
    rfl
  rwa [heq] at h

/-- The product-closure specialization required in `lem:occupation_logconcavity`:
a finite product of nonzero linear forms with nonnegative coefficients is
strongly log-concave. -/
theorem stronglyLogConcave_prod_nonnegativeLinearForm {m d : ℕ}
    (A : Fin m → Fin d → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) :
    StronglyLogConcave (∏ i : Fin m, nonnegativeLinearForm (A i)) := by
  have h := (completelyLogConcave_prod_X m).linearSubstitution A hA hrow
  have heq : linearSubstitution A (∏ i : Fin m, (X i : MvPolynomial (Fin m) ℝ)) =
      ∏ i : Fin m, nonnegativeLinearForm (A i) := by
    simp [linearSubstitution]
  rw [heq] at h
  exact h.stronglyLogConcave

end Parking

end
