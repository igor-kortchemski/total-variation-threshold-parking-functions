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

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Strong and complete log-concavity of polynomials

The two log-concavity notions are:
iterated partial derivatives, strong log-concavity (the strong log-concavity definition; [BH20, p. 23]), complete log-concavity ([BH20, p. 23]), M-convex sets and the
generating function `f_J` of a set of exponents ([BH20, pp. 9 and 31]).

The closure lemmas of complete log-concavity proved here need no external input:
stability under derivation in a nonnegative direction and under multiplication by a
positive constant, and the implication from complete to strong log-concavity.
-/

@[expose] public section

open MvPolynomial

namespace Parking

/-- The iterated partial derivative `∂^α f = ∂_{z_1}^{α_1} ⋯ ∂_{z_d}^{α_d} f`
(the strong log-concavity definition). -/
noncomputable def iteratedPDeriv {d : ℕ} (α : Fin d → ℕ) (f : MvPolynomial (Fin d) ℝ) :
    MvPolynomial (Fin d) ℝ :=
  (List.ofFn fun i => (pderiv i).toLinearMap ^ α i).prod f

/-- The positive orthant `(0, ∞)^d`. -/
def posOrthant (d : ℕ) : Set (Fin d → ℝ) :=
  {z | ∀ i, 0 < z i}

/-- Strong log-concavity (the strong log-concavity definition; [BH20, p. 23]):
nonnegative coefficients, and every iterated partial derivative is identically zero or has
a concave logarithm on the positive orthant. -/
def StronglyLogConcave {d : ℕ} (f : MvPolynomial (Fin d) ℝ) : Prop :=
  (∀ m, 0 ≤ f.coeff m) ∧
    ∀ α : Fin d → ℕ, iteratedPDeriv α f = 0 ∨
      ConcaveOn ℝ (posOrthant d) fun z => Real.log (eval z (iteratedPDeriv α f))

/-- M-convexity, through the exchange property ([BH20, p. 9]): for `α, β ∈ J` and
`α_i > β_i`, there is `j` with `α_j < β_j` and `α - e_i + e_j ∈ J`. -/
def IsMConvex {d : ℕ} (J : Set (Fin d →₀ ℕ)) : Prop :=
  ∀ α ∈ J, ∀ β ∈ J, ∀ i, β i < α i →
    ∃ j, α j < β j ∧ α - Finsupp.single i 1 + Finsupp.single j 1 ∈ J

/-- The generating function `f_J = ∑_{α ∈ J} w^α / α!` of a finite set of exponents, with
`α! = ∏_i α_i!` ([BH20, p. 31]; `lem:occupation_logconcavity`). -/
noncomputable def supportGenFun {d : ℕ} (J : Finset (Fin d →₀ ℕ)) : MvPolynomial (Fin d) ℝ :=
  ∑ α ∈ J, monomial α ((∏ i, ((α i).factorial : ℝ))⁻¹)

/-- The derivative in direction `v`, `D_v = ∑_i v_i ∂_i`. -/
noncomputable def dirDeriv {d : ℕ} (v : Fin d → ℝ) :
    MvPolynomial (Fin d) ℝ →ₗ[ℝ] MvPolynomial (Fin d) ℝ :=
  ∑ i, v i • (pderiv i).toLinearMap

/-- Complete log-concavity ([BH20, p. 23], after Anari, Gharan and Vinzant): nonnegative
coefficients, and for every finite sequence of nonnegative directions `v_1, …, v_r`,
`D_{v_1} ⋯ D_{v_r} f` is identically zero or has a concave logarithm on the positive
orthant. -/
def CompletelyLogConcave {d : ℕ} (f : MvPolynomial (Fin d) ℝ) : Prop :=
  (∀ m, 0 ≤ f.coeff m) ∧
    ∀ vs : List (Fin d → ℝ), (∀ v ∈ vs, ∀ i, 0 ≤ v i) →
      (vs.map dirDeriv).prod f = 0 ∨
        ConcaveOn ℝ (posOrthant d) fun z => Real.log (eval z ((vs.map dirDeriv).prod f))

variable {d : ℕ}

theorem dirDeriv_apply (v : Fin d → ℝ) (f : MvPolynomial (Fin d) ℝ) :
    dirDeriv v f = ∑ i, v i • pderiv i f := by
  simp [dirDeriv]

theorem dirDeriv_single (i : Fin d) : dirDeriv (Pi.single i 1) = (pderiv i).toLinearMap := by
  refine LinearMap.ext fun f => ?_
  rw [dirDeriv_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- A derivative in a nonnegative direction of a polynomial with nonnegative coefficients
has nonnegative coefficients. -/
theorem coeff_dirDeriv_nonneg {f : MvPolynomial (Fin d) ℝ} (hf : ∀ m, 0 ≤ f.coeff m)
    {v : Fin d → ℝ} (hv : ∀ i, 0 ≤ v i) (m : Fin d →₀ ℕ) : 0 ≤ (dirDeriv v f).coeff m := by
  rw [dirDeriv_apply, coeff_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [coeff_smul, coeff_pderiv, smul_eq_mul]
  exact mul_nonneg (hv i) (mul_nonneg (hf _) (by positivity))

theorem coeff_prod_dirDeriv_nonneg {f : MvPolynomial (Fin d) ℝ} (hf : ∀ m, 0 ≤ f.coeff m)
    {vs : List (Fin d → ℝ)} (hvs : ∀ v ∈ vs, ∀ i, 0 ≤ v i) (m : Fin d →₀ ℕ) :
    0 ≤ ((vs.map dirDeriv).prod f).coeff m := by
  induction vs generalizing m with
  | nil => simpa using hf m
  | cons v vs ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact coeff_dirDeriv_nonneg (fun m => ih (fun w hw => hvs w (by simp [hw])) m)
      (hvs v (by simp)) m

/-- A nonzero polynomial with nonnegative coefficients is positive on the positive
orthant. -/
theorem eval_pos_of_coeff_nonneg {g : MvPolynomial (Fin d) ℝ} (hg : ∀ m, 0 ≤ g.coeff m)
    (hg0 : g ≠ 0) {z : Fin d → ℝ} (hz : z ∈ posOrthant d) : 0 < eval z g := by
  rw [eval_eq]
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt support_eq_empty.1 hg0)
  refine Finset.sum_pos' (fun n _ => mul_nonneg (hg n) ?_) ⟨m, hm, ?_⟩
  · exact Finset.prod_nonneg fun i _ => pow_nonneg (hz i).le _
  · exact mul_pos (lt_of_le_of_ne (hg m) (Ne.symm (mem_support_iff.1 hm)))
      (Finset.prod_pos fun i _ => pow_pos (hz i) _)

namespace CompletelyLogConcave

/-- Complete log-concavity is stable under derivation in a nonnegative direction. -/
theorem dirDeriv {f : MvPolynomial (Fin d) ℝ} (hf : CompletelyLogConcave f) {b : Fin d → ℝ}
    (hb : ∀ i, 0 ≤ b i) : CompletelyLogConcave (Parking.dirDeriv b f) := by
  refine ⟨coeff_dirDeriv_nonneg hf.1 hb, fun vs hvs => ?_⟩
  have h := hf.2 (vs ++ [b]) (by
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact hvs v hv
    · rw [List.mem_singleton.1 hv]; exact hb)
  simpa only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Module.End.mul_apply] using h

/-- Complete log-concavity is stable under partial derivation. -/
theorem pderiv {f : MvPolynomial (Fin d) ℝ} (hf : CompletelyLogConcave f) (i : Fin d) :
    CompletelyLogConcave (MvPolynomial.pderiv i f) := by
  have h := hf.dirDeriv (b := Pi.single i 1) (fun j => by
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj])
  rwa [dirDeriv_single] at h

/-- Complete log-concavity is stable under multiplication by a positive constant. -/
theorem smul {f : MvPolynomial (Fin d) ℝ} (hf : CompletelyLogConcave f) {c : ℝ} (hc : 0 < c) :
    CompletelyLogConcave (c • f) := by
  refine ⟨fun m => by rw [coeff_smul, smul_eq_mul]; exact mul_nonneg hc.le (hf.1 m),
    fun vs hvs => ?_⟩
  have hlin : (vs.map Parking.dirDeriv).prod (c • f) = c • (vs.map Parking.dirDeriv).prod f :=
    LinearMap.map_smul _ c f
  rw [hlin]
  by_cases h0 : (vs.map Parking.dirDeriv).prod f = 0
  · left; rw [h0, smul_zero]
  · right
    rcases hf.2 vs hvs with h | hconc
    · exact absurd h h0
    have hS : Convex ℝ (posOrthant d) := hconc.1
    refine (hconc.add (concaveOn_const (Real.log c) hS)).congr fun z hz => ?_
    have hpos := eval_pos_of_coeff_nonneg (coeff_prod_dirDeriv_nonneg hf.1 hvs) h0 hz
    simp only [Pi.add_apply, smul_eval]
    rw [Real.log_mul hc.ne' hpos.ne', add_comm]

/-- Complete log-concavity implies strong log-concavity: `∂^α` is the composition of the
derivatives in the directions `e_i`, each repeated `α_i` times. -/
theorem stronglyLogConcave {f : MvPolynomial (Fin d) ℝ} (hf : CompletelyLogConcave f) :
    StronglyLogConcave f := by
  refine ⟨hf.1, fun α => ?_⟩
  let vs : List (Fin d → ℝ) :=
    (List.ofFn fun i => List.replicate (α i) (Pi.single i (1 : ℝ))).flatten
  have hvs : ∀ v ∈ vs, ∀ j, 0 ≤ v j := by
    intro v hv j
    obtain ⟨l, hl, hvl⟩ := List.mem_flatten.1 hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    rw [List.eq_of_mem_replicate hvl]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have heq : iteratedPDeriv α f = (vs.map Parking.dirDeriv).prod f := by
    simp only [iteratedPDeriv, vs, List.map_flatten, List.prod_flatten, List.map_ofFn,
      Function.comp_def, List.map_replicate, List.prod_replicate, dirDeriv_single]
  rw [heq]
  exact hf.2 vs hvs

end CompletelyLogConcave

end Parking

end
