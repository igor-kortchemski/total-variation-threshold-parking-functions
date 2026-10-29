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

public import Parking.CLCCriterion
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Analytic consequences of strong log-concavity

The definitions remain the coordinate-derivative and directional-derivative
notions from `Parking.LogConcave`. The analytic Hessian implication below is
adapted from the parallel formalization
`ParkingThreshold.ParkingLogConcavity`; the source and its hash are recorded in
`docs/PROVENANCE.md`. The multiset-of-derivatives bridge is proved here.
-/

@[expose] public section

open MvPolynomial Filter Topology Set

namespace Parking

theorem isOpen_posOrthant (d : ℕ) : IsOpen (posOrthant d) := by
  have heq : posOrthant d = ⋂ i : Fin d, {z : Fin d → ℝ | 0 < z i} := by
    ext z
    simp [posOrthant]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

/-- Log-concavity implies the directional Hessian inequality at every point of
the positive orthant. -/
theorem dirDeriv_inequality_of_concaveOn_log_eval {d : ℕ}
    (f : MvPolynomial (Fin d) ℝ)
    (hpos : ∀ z ∈ posOrthant d, 0 < eval z f)
    (hconc : ConcaveOn ℝ (posOrthant d) fun z => Real.log (eval z f))
    (x : Fin d → ℝ) (hx : x ∈ posOrthant d) (v : Fin d → ℝ) :
    eval x f * eval x (dirDeriv v (dirDeriv v f)) ≤ (eval x (dirDeriv v f)) ^ 2 := by
  let D : Set ℝ := {t | x + t • v ∈ posOrthant d}
  let L := AffineMap.lineMap x (x + v) (k := ℝ)
  have hL (t : ℝ) : L t = x + t • v := by
    simp only [L, AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  have hc : ConcaveOn ℝ D (fun t => Real.log (eval (x + t • v) f)) := by
    have hLD : L ⁻¹' posOrthant d = D := by
      ext t
      change L t ∈ posOrthant d ↔ x + t • v ∈ posOrthant d
      rw [hL]
    have h := hconc.comp_affineMap L
    rw [hLD] at h
    simpa only [Function.comp_def, hL] using h
  have hd (t : ℝ) (ht : t ∈ D) :
      HasDerivAt (fun s => Real.log (eval (x + s • v) f))
        (eval (x + t • v) (dirDeriv v f) / eval (x + t • v) f) t :=
    (hasDerivAt_eval_add_smul f x v t).log (hpos _ ht).ne'
  have hanti : AntitoneOn
      (fun t => eval (x + t • v) (dirDeriv v f) / eval (x + t • v) f) D := by
    intro s hs t ht hst
    dsimp only
    rw [← (hd s hs).deriv, ← (hd t ht).deriv]
    exact hc.antitoneOn_deriv (fun u hu => (hd u hu).differentiableAt) hs ht hst
  have hD : D ∈ 𝓝 (0 : ℝ) := by
    have hcont : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h := (hcont.continuousAt (x := (0 : ℝ))).preimage_mem_nhds
      ((isOpen_posOrthant d).mem_nhds (by simpa only [zero_smul, add_zero] using hx))
    exact h
  have hderiv := (hasDerivAt_eval_add_smul (dirDeriv v f) x v (0 : ℝ)).fun_div
    (hasDerivAt_eval_add_smul f x v 0)
    (by simpa only [zero_smul, add_zero] using (hpos x hx).ne')
  have hnonpos := hanti.derivWithin_nonpos (x := (0 : ℝ))
  rw [derivWithin_of_mem_nhds hD, hderiv.deriv] at hnonpos
  simp only [zero_smul, add_zero] at hnonpos
  have hn := (div_le_iff₀ (sq_pos_of_pos (hpos x hx))).mp hnonpos
  nlinarith only [hn]

/-- Exact analytic characterization of polynomial log-concavity using directional
second derivatives, under positivity on the positive orthant. -/
theorem concaveOn_log_eval_iff_dirDeriv_inequality {d : ℕ}
    (f : MvPolynomial (Fin d) ℝ) (hpos : ∀ z ∈ posOrthant d, 0 < eval z f) :
    (ConcaveOn ℝ (posOrthant d) fun z => Real.log (eval z f)) ↔
      ∀ z ∈ posOrthant d, ∀ v : Fin d → ℝ,
        eval z f * eval z (dirDeriv v (dirDeriv v f)) ≤ (eval z (dirDeriv v f)) ^ 2 :=
  ⟨fun h => dirDeriv_inequality_of_concaveOn_log_eval f hpos h,
    concaveOn_log_eval_of_sq_le hpos⟩


/-- Coordinate partial derivatives commute as linear operators. -/
theorem pderiv_linearMap_commute {d : ℕ} (i j : Fin d) :
    Commute ((pderiv i).toLinearMap : Module.End ℝ (MvPolynomial (Fin d) ℝ))
      ((pderiv j).toLinearMap : Module.End ℝ (MvPolynomial (Fin d) ℝ)) := by
  apply LinearMap.ext
  intro f
  exact pderiv_comm i j f

/-- The multi-index definition equals any ordered word of partial derivatives
having the same multiplicities. -/
theorem prod_pderiv_eq_iteratedPDeriv {d : ℕ} (is : List (Fin d))
    (f : MvPolynomial (Fin d) ℝ) :
    (is.map (fun i => (pderiv i).toLinearMap)).prod f =
      iteratedPDeriv (fun i => is.count i) f := by
  let js : List (Fin d) :=
    (List.ofFn fun i : Fin d => List.replicate (is.count i) i).flatten
  have hp : js.Perm is := by
    apply List.perm_iff_count.mpr
    intro i
    simp [js, List.count_flatten, List.map_ofFn, List.sum_ofFn, List.count_replicate]
  have hc : (js.map fun i => ((pderiv i).toLinearMap : Module.End ℝ (MvPolynomial (Fin d) ℝ))).Pairwise Commute := by
    apply List.pairwise_map.mpr
    apply List.pairwise_of_forall
    intro i j
    exact pderiv_linearMap_commute i j
  have heq := (hp.map fun i => ((pderiv i).toLinearMap : Module.End ℝ (MvPolynomial (Fin d) ℝ))).prod_eq' hc
  rw [← heq]
  simp only [js, List.map_flatten, List.prod_flatten, List.map_ofFn, Function.comp_def,
    List.map_replicate, List.prod_replicate, iteratedPDeriv]

/-- Strong log-concavity controls every finite word of coordinate derivatives,
independently of the order of that word. -/
theorem StronglyLogConcave.list_pderiv {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : StronglyLogConcave f) (is : List (Fin d)) :
    (is.map (fun i => (pderiv i).toLinearMap)).prod f = 0 ∨
      ConcaveOn ℝ (posOrthant d)
        (fun z => Real.log (eval z ((is.map (fun i => (pderiv i).toLinearMap)).prod f))) := by
  rw [prod_pderiv_eq_iteratedPDeriv]
  exact hf.2 _

/-- Strong log-concavity is closed under coordinate differentiation. -/
theorem StronglyLogConcave.pderiv {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : StronglyLogConcave f) (i : Fin d) : StronglyLogConcave (pderiv i f) := by
  refine ⟨coeff_pderiv_nonneg hf.1 i, fun α => ?_⟩
  let js : List (Fin d) := (List.ofFn fun j => List.replicate (α j) j).flatten
  have h := hf.list_pderiv (js ++ [i])
  simpa only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply,
    js, List.map_flatten, List.prod_flatten, List.map_ofFn, Function.comp_def,
    List.map_replicate, List.prod_replicate, iteratedPDeriv, Derivation.coeFn_coe] using h

/-- The order-zero consequence of strong log-concavity. -/
theorem StronglyLogConcave.concaveOn_log_eval {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : StronglyLogConcave f) (hf0 : f ≠ 0) :
    ConcaveOn ℝ (posOrthant d) (fun z => Real.log (eval z f)) := by
  rcases hf.list_pderiv [] with h | h
  · exact False.elim (hf0 (by simpa using h))
  · simpa using h

/-- Directional derivatives are additive in their direction. -/
theorem dirDeriv_add_direction {d : ℕ} (u v : Fin d → ℝ)
    (f : MvPolynomial (Fin d) ℝ) :
    dirDeriv (u + v) f = dirDeriv u f + dirDeriv v f := by
  rw [dirDeriv_add, LinearMap.add_apply]

/-- Directional derivatives are homogeneous in their direction. -/
theorem dirDeriv_smul_direction {d : ℕ} (c : ℝ) (v : Fin d → ℝ)
    (f : MvPolynomial (Fin d) ℝ) :
    dirDeriv (c • v) f = c • dirDeriv v f := by
  rw [dirDeriv_smul, LinearMap.smul_apply]

/-- The symmetric Hessian bilinear form of polynomial evaluation. -/
noncomputable def polynomialHessian {d : ℕ} (f : MvPolynomial (Fin d) ℝ)
    (x : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => eval x (dirDeriv u (dirDeriv v f))
      map_add' := by
        intro v w
        rw [dirDeriv_add_direction]
        simp only [map_add]
      map_smul' := by
        intro c v
        rw [dirDeriv_smul_direction, (dirDeriv u).map_smul]
        simp only [smul_eq_C_mul, map_mul, eval_C, smul_eq_mul, RingHom.id_apply] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    change eval x (dirDeriv (u + v) (dirDeriv w f)) = _
    rw [dirDeriv_add_direction, map_add]
    rfl
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    change eval x (dirDeriv (c • u) (dirDeriv v f)) = _
    rw [dirDeriv_smul_direction, smul_eq_C_mul, map_mul, eval_C]
    rfl

theorem polynomialHessian_apply {d : ℕ} (f : MvPolynomial (Fin d) ℝ)
    (x u v : Fin d → ℝ) :
    polynomialHessian f x u v = eval x (dirDeriv u (dirDeriv v f)) := rfl

theorem polynomialHessian_symm {d : ℕ} (f : MvPolynomial (Fin d) ℝ)
    (x u v : Fin d → ℝ) : polynomialHessian f x u v = polynomialHessian f x v u := by
  simp only [polynomialHessian_apply, dirDeriv_comm f u v]

theorem polynomialHessian_self_left {d n : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : f.IsHomogeneous n) (x v : Fin d → ℝ) :
    polynomialHessian f x x v = ((n - 1 : ℕ) : ℝ) * eval x (dirDeriv v f) :=
  eval_dirDeriv_self (isHomogeneous_dirDeriv hf v) x

theorem polynomialHessian_self_self {d n : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : f.IsHomogeneous n) (x : Fin d → ℝ) :
    polynomialHessian f x x x = ((n - 1 : ℕ) : ℝ) * (n : ℝ) * eval x f := by
  rw [polynomialHessian_self_left hf, eval_dirDeriv_self hf, mul_assoc]

section Bilinear

open LinearMap.BilinForm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Transfer nonpositivity from an arbitrary hyperplane to the orthogonal
hyperplane of a vector with positive square. -/
theorem bilin_nonpos_of_orthogonal
    (B : LinearMap.BilinForm ℝ E) (hB : ∀ u v, B u v = B v u)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ∀ w, ℓ w = 0 → B w w ≤ 0)
    {x : E} (hx : 0 < B x x) {w : E} (hw : B x w = 0) : B w w ≤ 0 := by
  have hℓx : ℓ x ≠ 0 := by
    intro h
    exact (not_lt_of_ge (hℓ x h)) hx
  have hz : ℓ (ℓ w • x - ℓ x • w) = 0 := by simp [mul_comm]
  have hq := hℓ _ hz
  have hwx : B w x = 0 := by rw [hB w x, hw]
  simp only [sub_left, sub_right, smul_left, smul_right, hw, hwx,
    mul_zero, sub_zero, zero_sub] at hq
  have hs : 0 < (ℓ x) ^ 2 := sq_pos_of_ne_zero hℓx
  have hp : 0 ≤ (ℓ w) ^ 2 * B x x := mul_nonneg (sq_nonneg _) hx.le
  have hn : (ℓ x) ^ 2 * B w w ≤ 0 := by nlinarith
  exact nonpos_of_mul_nonpos_right hn hs

/-- Reverse Cauchy–Schwarz, using nonpositivity on a hyperplane instead of an
eigenvalue hypothesis. -/
theorem bilin_reverse_cauchySchwarz
    (B : LinearMap.BilinForm ℝ E) (hB : ∀ u v, B u v = B v u)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ∀ w, ℓ w = 0 → B w w ≤ 0)
    {x : E} (hx : 0 < B x x) (v : E) :
    B x x * B v v ≤ (B x v) ^ 2 := by
  have hxx : B x x ≠ 0 := ne_of_gt hx
  have hw : B x (v - (B x v / B x x) • x) = 0 := by
    rw [sub_right, smul_right, div_mul_cancel₀ _ hxx, sub_self]
  have hq := bilin_nonpos_of_orthogonal B hB ℓ hℓ hx hw
  rw [sub_left, sub_right, smul_right, smul_left, sub_right, smul_right,
    hB v x] at hq
  have hc : 0 < (B x x) ^ 2 := sq_pos_of_pos hx
  have hm := mul_nonpos_of_nonneg_of_nonpos hc.le hq
  have hid :
      (B x x) ^ 2 *
        (B v v - (B x v / B x x) * B x v -
          (B x v / B x x) * (B x v - (B x v / B x x) * B x x)) =
        B x x * (B x x * B v v - (B x v) ^ 2) := by
    field_simp
    ring
  rw [hid] at hm
  have : B x x * B v v - (B x v) ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hm hx
  linarith

end Bilinear

/-- A homogeneous strongly log-concave polynomial has a reverse-Cauchy–Schwarz
Hessian at every point of the positive orthant. The proof derives nonpositivity
on the hyperplane orthogonal to the radial Hessian vector. -/
theorem StronglyLogConcave.revCS_polynomialHessian {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m) (hm : 2 ≤ m)
    {x : Fin d → ℝ} (hx : x ∈ posOrthant d) :
    RevCS (fun u v => polynomialHessian f x u v) := by
  by_cases hf0 : f = 0
  · subst f
    intro u v hu
    simp [polynomialHessian_apply] at hu
  have hpos : ∀ z ∈ posOrthant d, 0 < eval z f :=
    fun z hz => eval_pos_of_coeff_nonneg hf.1 hf0 hz
  have hlog := hf.concaveOn_log_eval hf0
  have hm1 : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (by omega : 0 < m - 1)
  have horth : ∀ v, polynomialHessian f x x v = 0 → polynomialHessian f x v v ≤ 0 := by
    intro v hv
    rw [polynomialHessian_self_left hhom] at hv
    have hv0 : eval x (dirDeriv v f) = 0 :=
      (mul_eq_zero.mp hv).resolve_left hm1.ne'
    have hineq := dirDeriv_inequality_of_concaveOn_log_eval f hpos hlog x hx v
    rw [hv0, zero_pow (by decide : 2 ≠ 0)] at hineq
    exact nonpos_of_mul_nonpos_right hineq (hpos x hx)
  intro u v hu
  exact bilin_reverse_cauchySchwarz (polynomialHessian f x) (polynomialHessian_symm f x)
    (polynomialHessian f x x) horth hu v

end Parking

end
