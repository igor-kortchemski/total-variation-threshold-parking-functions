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

public import Parking.Paper.QuadraticSignature
public import Parking.Paper.StrongCompleteEquivalence
public import Parking.Paper.SupportNormalization

/-!
# The intrinsic algebraic Lorentzian condition

We use the intrinsic characterization of Brändén–Huh: homogeneous polynomials
with nonnegative coefficients, M-convex support, and positive index at most one
for the Hessian of every quadratic coordinate derivative. Positive index is
Mathlib's maximal dimension of a positive-definite subspace, independently of
both analytic log-concavity notions. The reverse-Cauchy–Schwarz equivalence is
proved in `QuadraticSignature`.
-/

@[expose] public section

open MvPolynomial

namespace Parking

/-- The genuine algebraic Lorentzian condition in degree `m` ([BH20, Theorem 2.25]).
Every quadratic coordinate derivative has a Hessian of positive index at most one.
For degrees zero and one this last condition is vacuous. -/
def Lorentzian {d : ℕ} (m : ℕ) (f : MvPolynomial (Fin d) ℝ) : Prop :=
  f.IsHomogeneous m ∧ (∀ α, 0 ≤ f.coeff α) ∧
    IsMConvex (f.support : Set (Fin d →₀ ℕ)) ∧
    ∀ is : List (Fin d), is.length + 2 = m →
      sigPos (LinearMap.BilinMap.toQuadraticMap
        (polynomialHessian ((is.map (fun i => (pderiv i).toLinearMap)).prod f) 0)) ≤ 1

/-- Over the reals, differentiation contracts the exponent support. -/
theorem support_pderiv_eq_contractSet {d : ℕ} (f : MvPolynomial (Fin d) ℝ)
    (i : Fin d) : (pderiv i f).support = contractSet f.support i := by
  ext α
  rw [mem_support_iff, mem_contractSet, mem_support_iff, coeff_pderiv]
  have hfac : (α i : ℝ) + 1 ≠ 0 := by positivity
  simp only [ne_eq, mul_eq_zero, hfac, or_false]

/-- Normalizing the nonzero coefficients preserves the support exactly. -/
theorem support_supportGenFun {d : ℕ} (J : Finset (Fin d →₀ ℕ)) :
    (supportGenFun J).support = J := by
  ext α
  rw [mem_support_iff, coeff_supportGenFun_ite]
  by_cases hα : α ∈ J
  · simp only [hα, ↓reduceIte, iff_true]
    positivity
  · simp [hα]

/-- Two polynomials with identical supports have the same vanishing behavior. -/
theorem ne_zero_iff_of_support_eq {d : ℕ} {f g : MvPolynomial (Fin d) ℝ}
    (h : f.support = g.support) : f ≠ 0 ↔ g ≠ 0 := by
  rw [← support_nonempty, ← support_nonempty, h]

/-- Active-variable connectivity from M-convexity depends only on support, not
on the particular positive coefficient values. -/
theorem IsMConvex.reflTransGen_pderiv_of_support {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hM : IsMConvex (f.support : Set (Fin d →₀ ℕ)))
    (hhom : f.IsHomogeneous m) (hm : 2 ≤ m) (i j : Fin d)
    (hi : pderiv i f ≠ 0) (hj : pderiv j f ≠ 0) :
    Relation.ReflTransGen (fun a b => pderiv a (pderiv b f) ≠ 0) i j := by
  have hs (a : Fin d) :
      (pderiv a f).support = (pderiv a (supportGenFun f.support)).support := by
    simp only [support_pderiv_eq_contractSet, support_supportGenFun]
  have hdeg : ∀ α ∈ f.support, α.degree = m := by
    intro α hα
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hhom (mem_support_iff.mp hα)
  have h := hM.reflTransGen_pderiv hm hdeg i j
    ((ne_zero_iff_of_support_eq (hs i)).1 hi)
    ((ne_zero_iff_of_support_eq (hs j)).1 hj)
  exact Relation.ReflTransGen.mono (fun a b hab =>
    (ne_zero_iff_of_support_eq (by simp only [support_pderiv_eq_contractSet,
      support_supportGenFun])).2 hab) i j h

/-- The intrinsic Lorentzian condition is preserved by coordinate derivatives. -/
theorem Lorentzian.pderiv {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : Lorentzian m f) (i : Fin d) : Lorentzian (m - 1) (pderiv i f) := by
  refine ⟨hf.1.pderiv, coeff_pderiv_nonneg hf.2.1 i, ?_, ?_⟩
  · rw [support_pderiv_eq_contractSet]
    exact hf.2.2.1.contractSet i
  · intro is his
    have hlen : (is ++ [i]).length + 2 = m := by
      rw [List.length_append, List.length_singleton]
      omega
    simpa only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply,
      Derivation.coeFn_coe] using hf.2.2.2 (is ++ [i]) hlen

/-- The quadratic Lorentzian condition controls its constant mixed Hessian. -/
theorem Lorentzian.revCS_mixedForm_two {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : Lorentzian 2 f) : RevCS (mixedForm f []) := by
  have hsig := hf.2.2.2 [] (by simp)
  simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at hsig
  have h := (sigPos_le_one_iff_revCS (polynomialHessian f 0)
    (polynomialHessian_symm f 0)).1 hsig
  simpa only [RevCS, mixedForm, List.map_nil, List.prod_nil, Module.End.one_apply,
    polynomialHessian_apply] using h

/-- Perron induction upgrades the coordinate-quadratic algebraic condition to
all positive mixed directions. M-convexity supplies its connectivity hypothesis. -/
theorem Lorentzian.revCS_mixedForm {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : Lorentzian m f) (us : List (Fin d → ℝ)) (hus : us.length + 2 = m)
    (hpos : ∀ u ∈ us, ∀ i, 0 < u i) : RevCS (mixedForm f us) := by
  induction m generalizing f us with
  | zero => omega
  | succ m ih =>
    rcases List.eq_nil_or_concat' us with rfl | ⟨us', w, rfl⟩
    · have hm : m + 1 = 2 := by simpa using hus.symm
      rw [hm] at hf
      exact hf.revCS_mixedForm_two
    · rw [List.length_append, List.length_singleton] at hus
      have hlen : us'.length + 2 = m := by omega
      have hpos' : ∀ u ∈ us', ∀ i, 0 < u i := fun u hu =>
        hpos u (List.mem_append_left _ hu)
      have hw : ∀ i, 0 < w i := hpos w (List.mem_append_right _ (List.mem_singleton_self w))
      refine revCS_mixedForm_append_of_pderiv hf.1 hf.2.1 (by omega) hpos' hw
        (hf.2.2.1.reflTransGen_pderiv_of_support hf.1 (by omega)) fun k => ?_
      exact ih (by simpa using hf.pderiv k) us' hlen hpos'

/-- Intrinsic algebraic Lorentzian polynomials are completely log-concave. -/
theorem Lorentzian.completelyLogConcave {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : Lorentzian m f) : CompletelyLogConcave f :=
  completelyLogConcave_of_revCS f hf.2.1 hf.1 hf.revCS_mixedForm

/-- Intrinsic algebraic Lorentzian polynomials are strongly log-concave. -/
theorem Lorentzian.stronglyLogConcave {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : Lorentzian m f) : StronglyLogConcave f :=
  hf.completelyLogConcave.stronglyLogConcave

/-- A coordinate-derivative word preserves strong log-concavity. -/
theorem StronglyLogConcave.prod_pderiv {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : StronglyLogConcave f) (is : List (Fin d)) :
    StronglyLogConcave ((is.map (fun i => (MvPolynomial.pderiv i).toLinearMap)).prod f) := by
  induction is with
  | nil => simpa using hf
  | cons i is ih =>
    simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply,
      Derivation.coeFn_coe] using ih.pderiv i

/-- Coordinate differentiation lowers the homogeneous degree by the word length. -/
theorem isHomogeneous_prod_pderiv {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hhom : f.IsHomogeneous m) (is : List (Fin d)) :
    ((is.map (fun i => (pderiv i).toLinearMap)).prod f).IsHomogeneous (m - is.length) := by
  induction is with
  | nil => simpa using hhom
  | cons i is ih =>
    simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply,
      Derivation.coeFn_coe, List.length_cons, Nat.sub_sub] using ih.pderiv (i := i)

/-- A quadratic polynomial has a constant Hessian. -/
theorem polynomialHessian_eq_of_isHomogeneous_two {d : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : f.IsHomogeneous 2) (x y : Fin d → ℝ) :
    polynomialHessian f x = polynomialHessian f y := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  rw [polynomialHessian_apply, polynomialHessian_apply]
  have hconst : (dirDeriv u (dirDeriv v f)).IsHomogeneous 0 := by
    simpa using isHomogeneous_dirDeriv (isHomogeneous_dirDeriv hf v) u
  have hC := totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hconst)
  rw [hC]
  simp

/-- The analytic hypothesis implies the independent quadratic signature
condition. The support exchange property is the separate combinatorial step in
[BH20, Theorem 2.30], made explicit in this intermediate lemma. -/
theorem StronglyLogConcave.lorentzian_of_isMConvex {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m) (hM : IsMConvex (f.support : Set (Fin d →₀ ℕ))) :
    Lorentzian m f := by
  refine ⟨hhom, hf.1, hM, fun is his => ?_⟩
  have hhom' : MvPolynomial.IsHomogeneous
      ((is.map (fun i => (MvPolynomial.pderiv i).toLinearMap)).prod f) 2 := by
    convert isHomogeneous_prod_pderiv hhom is using 1
    omega
  apply sigPos_le_one_of_revCS
  rw [polynomialHessian_eq_of_isHomogeneous_two hhom' 0 1]
  exact (hf.prod_pderiv is).revCS_polynomialHessian hhom' le_rfl
    (x := (1 : Fin d → ℝ)) (fun _ => zero_lt_one)

/-- [BH20, Theorem 2.30]: homogeneous strong log-concavity implies the genuine
intrinsic Lorentzian property. Its support premise is proved from strong
log-concavity, rather than added to the source hypothesis. -/
theorem StronglyLogConcave.lorentzian {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : StronglyLogConcave f) (hhom : f.IsHomogeneous m) : Lorentzian m f :=
  hf.lorentzian_of_isMConvex hhom (hf.isMConvex_support hhom)

/-- The manuscript's homogeneous strong/Lorentzian equivalence. The predicates
have independent analytic and algebraic definitions. -/
theorem stronglyLogConcave_iff_lorentzian {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hhom : f.IsHomogeneous m) : StronglyLogConcave f ↔ Lorentzian m f :=
  ⟨fun h => h.lorentzian hhom, fun h => h.stronglyLogConcave⟩

/-- The complete/Lorentzian part of [BH20, Theorem 2.30]. -/
theorem completelyLogConcave_iff_lorentzian {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hhom : f.IsHomogeneous m) : CompletelyLogConcave f ↔ Lorentzian m f :=
  ⟨fun h => h.stronglyLogConcave.lorentzian hhom, fun h => h.completelyLogConcave⟩

/-- Nonnegative directional differentiation preserves algebraic Lorentzianity. -/
theorem Lorentzian.dirDeriv {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : Lorentzian m f) {v : Fin d → ℝ} (hv : ∀ i, 0 ≤ v i) :
    Lorentzian (m - 1) (Parking.dirDeriv v f) :=
  (hf.completelyLogConcave.dirDeriv hv).stronglyLogConcave.lorentzian
    (isHomogeneous_dirDeriv hf.1 v)

/-- Positive scaling preserves the genuine Lorentzian property. -/
theorem Lorentzian.smul {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : Lorentzian m f) {c : ℝ} (hc : 0 < c) : Lorentzian m (c • f) := by
  apply (hf.completelyLogConcave.smul hc).stronglyLogConcave.lorentzian_of_isMConvex
  · simpa only [smul_eq_C_mul] using hf.1.C_mul c
  · simpa only [support_smul_eq hc.ne'] using hf.2.2.1

/-- The factorial-normalized generating polynomial of any homogeneous M-convex
support is algebraically Lorentzian. This is the normalized-support direction of
[BH20, Theorem 3.10] and does not depend on any parking occupation conclusion. -/
theorem lorentzian_supportGenFun {d m : ℕ} (J : Finset (Fin d →₀ ℕ))
    (hdeg : ∀ α ∈ J, α.degree = m) (hM : IsMConvex (J : Set (Fin d →₀ ℕ))) :
    Lorentzian m (supportGenFun J) := by
  have hclc := completelyLogConcave_of_revCS (supportGenFun J)
    (coeff_supportGenFun_nonneg J) (isHomogeneous_supportGenFun hdeg)
    (revCS_mixedForm_supportGenFun J hdeg hM)
  apply hclc.stronglyLogConcave.lorentzian_of_isMConvex (isHomogeneous_supportGenFun hdeg)
  simpa only [support_supportGenFun] using hM

/-- Every nonzero coordinate derivative of a strongly log-concave polynomial
is strictly positive on the positive orthant (the strong log-concavity definition). -/
theorem StronglyLogConcave.eval_iteratedPDeriv_pos {d : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f) (α : Fin d → ℕ)
    (hne : iteratedPDeriv α f ≠ 0) {x : Fin d → ℝ} (hx : x ∈ posOrthant d) :
    0 < eval x (iteratedPDeriv α f) := by
  let is := (List.ofFn fun i : Fin d => List.replicate (α i) i).flatten
  have heq : ((is.map (fun i => (MvPolynomial.pderiv i).toLinearMap)).prod f) =
      iteratedPDeriv α f := by
    simp only [is, List.map_flatten, List.prod_flatten, List.map_ofFn,
      Function.comp_def, List.map_replicate, List.prod_replicate, iteratedPDeriv]
  have hder := hf.prod_pderiv is
  rw [heq] at hder
  exact eval_pos_of_coeff_nonneg hder.1 hne hx

end Parking

end
