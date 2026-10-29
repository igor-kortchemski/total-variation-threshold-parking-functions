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

public import Parking.Paper.StrongLogConcavity
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Connectivity forced by log-concavity

A nonnegative symmetric matrix with the reverse Cauchy–Schwarz property has
only one component with a nonzero row. Applying this to the Hessian yields the
connectivity needed by the Perron induction, without assuming M-convexity.
-/

@[expose] public section

open Matrix MvPolynomial

namespace Parking

/-- A nonnegative reverse-Cauchy–Schwarz matrix connects any two nonzero rows.
Two separate components would give positive quadratic forms with zero mixed
product, contradicting reverse Cauchy–Schwarz. -/
theorem reflTransGen_of_revCS {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ k l, 0 ≤ A k l) (hsymm : A.IsSymm)
    (hB : RevCS (fun x y => x ⬝ᵥ (A *ᵥ y)))
    (i j : Fin d) (hi : 0 < ∑ l, A i l) (hj : 0 < ∑ l, A j l) :
    Relation.ReflTransGen (fun k l => 0 < A k l) i j := by
  classical
  by_contra hij
  let S : Fin d → Prop := fun k => Relation.ReflTransGen (fun k l => 0 < A k l) i k
  have hSi : S i := Relation.ReflTransGen.refl
  have hSj : ¬ S j := hij
  have hcross : ∀ k l, S k → ¬ S l → A k l = 0 := by
    intro k l hk hl
    by_contra hne
    exact hl (hk.tail (lt_of_le_of_ne (hA k l) (Ne.symm hne)))
  let u : Fin d → ℝ := fun k => if S k then 1 else 0
  let v : Fin d → ℝ := fun k => if S k then 0 else 1
  let r : Fin d → ℝ := fun k => ∑ l, A k l
  have hr : ∀ k, 0 ≤ r k := fun k => Finset.sum_nonneg fun l _ => hA k l
  have hu : ∀ k, 0 ≤ u k := by intro k; dsimp [u]; split_ifs <;> positivity
  have hv : ∀ k, 0 ≤ v k := by intro k; dsimp [v]; split_ifs <;> positivity
  have hAu (k : Fin d) : (A *ᵥ u) k = if S k then r k else 0 := by
    simp only [mulVec, dotProduct]
    by_cases hk : S k
    · simp only [hk, ↓reduceIte]
      change (∑ l, A k l * u l) = ∑ l, A k l
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : S l
      · simp [u, hl]
      · simp [u, hl, hcross k l hk hl]
    · simp only [hk, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : S l
      · rw [← hsymm.apply k l]
        simp [u, hl, hcross l k hl hk]
      · simp [u, hl]
  have huv : u + v = 1 := by
    ext k
    by_cases hk : S k <;> simp [u, v, hk]
  have hAv (k : Fin d) : (A *ᵥ v) k = if S k then 0 else r k := by
    have h := congrFun (mulVec_add A u v) k
    rw [huv] at h
    have hAone : (A *ᵥ (1 : Fin d → ℝ)) k = r k := by simp [mulVec, dotProduct, r]
    rw [hAone, Pi.add_apply, hAu] at h
    by_cases hk : S k <;> simp only [hk, ↓reduceIte] at h ⊢ <;> linarith
  have hposu : 0 < u ⬝ᵥ (A *ᵥ u) := by
    apply Finset.sum_pos'
    · intro k _
      rw [hAu]
      exact mul_nonneg (hu k) (by split_ifs; exact hr k; exact le_rfl)
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      simpa [u, hSi, hAu, r] using hi
  have hposv : 0 < v ⬝ᵥ (A *ᵥ v) := by
    apply Finset.sum_pos'
    · intro k _
      rw [hAv]
      exact mul_nonneg (hv k) (by split_ifs; exact le_rfl; exact hr k)
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      simpa [v, hSj, hAv, r] using hj
  have hzero : u ⬝ᵥ (A *ᵥ v) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hAv]
    by_cases hk : S k <;> simp [u, hk]
  have h := hB u v hposu
  change (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) ≤ (u ⬝ᵥ (A *ᵥ v)) ^ 2 at h
  rw [hzero, zero_pow (by decide : 2 ≠ 0)] at h
  exact (not_le_of_gt (mul_pos hposu hposv)) h

/-- Expansion of the Hessian in the coordinate basis. -/
theorem polynomialHessian_eq_dotProduct {d : ℕ} (f : MvPolynomial (Fin d) ℝ)
    (x u v : Fin d → ℝ) :
    polynomialHessian f x u v =
      u ⬝ᵥ ((Matrix.of fun i j => eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv j f))) *ᵥ v) := by
  simp only [polynomialHessian_apply, dirDeriv_apply, map_sum, Derivation.map_smul,
    smul_eval, Finset.mul_sum, mulVec, dotProduct, of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The graph of nonzero second partial derivatives of a homogeneous strongly
log-concave polynomial connects all variables that occur in it. -/
theorem StronglyLogConcave.reflTransGen_pderiv {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m) (hm : 2 ≤ m)
    (i j : Fin d) (hi : MvPolynomial.pderiv i f ≠ 0) (hj : MvPolynomial.pderiv j f ≠ 0) :
    Relation.ReflTransGen (fun k l => MvPolynomial.pderiv k (MvPolynomial.pderiv l f) ≠ 0) i j := by
  let A : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.of fun k l => eval 1 (MvPolynomial.pderiv k (MvPolynomial.pderiv l f))
  have hpos : (1 : Fin d → ℝ) ∈ posOrthant d := fun _ => zero_lt_one
  have hA : ∀ k l, 0 ≤ A k l := by
    intro k l
    by_cases hzero : MvPolynomial.pderiv k (MvPolynomial.pderiv l f) = 0
    · simp [A, hzero]
    · exact (eval_pos_of_coeff_nonneg
        (coeff_pderiv_nonneg (coeff_pderiv_nonneg hf.1 l) k) hzero hpos).le
  have hs : A.IsSymm := by
    ext k l
    exact congrArg (eval 1) (pderiv_comm l k f)
  have hB : RevCS (fun u v => u ⬝ᵥ (A *ᵥ v)) := by
    intro u v huv
    have hu : 0 < polynomialHessian f 1 u u := by
      simpa only [polynomialHessian_eq_dotProduct] using huv
    simpa only [polynomialHessian_eq_dotProduct] using
      hf.revCS_polynomialHessian hhom hm hpos u v hu
  have hrow (k : Fin d) (hk : MvPolynomial.pderiv k f ≠ 0) : 0 < ∑ l, A k l := by
    have heq : ∑ l, A k l = polynomialHessian f 1 (Pi.single k 1) 1 := by
      rw [polynomialHessian_eq_dotProduct]
      simp [dotProduct, mulVec, A, Pi.single_apply]
    rw [heq, polynomialHessian_symm, polynomialHessian_self_left hhom,
      dirDeriv_single, Derivation.coeFn_coe]
    exact mul_pos (by exact_mod_cast (by omega : 0 < m - 1))
      (eval_pos_of_coeff_nonneg (coeff_pderiv_nonneg hf.1 k) hk hpos)
  have hpath := reflTransGen_of_revCS A hA hs hB i j (hrow i hi) (hrow j hj)
  refine Relation.ReflTransGen.mono (fun k l hkl => ?_) i j hpath
  intro hzero
  simp [A, hzero] at hkl

end Parking

end
