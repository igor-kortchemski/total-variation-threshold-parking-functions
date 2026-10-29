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

public import Parking.LogConcave
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# The mixed form of a polynomial

For a polynomial `f` in `d`
variables and a list of directions `us = [u₁, …, u_r]`, the mixed form is the number

  `mixedForm f us x y = D_x D_y D_{u₁} ⋯ D_{u_r} f (0)`,

where `D_v = ∑_i v_i ∂_i` is `dirDeriv v`. When `f` is homogeneous of degree `r + 2`, the
polynomial `D_x D_y D_{u₁} ⋯ D_{u_r} f` is a constant, and `eval 0` reads it.

Main results:

- commutation: `pderiv_comm`, `dirDeriv_comm`, and the permutation invariance
  `mixedForm_perm`;
- the identities: `mixedForm_append` (Euler decomposition along the last
  direction, without commutation) and `mixedForm_pderiv` (`B_k(x, w) = B(x, e_k)`);
- symmetry `mixedForm_comm`, linearity in `x`, `y` (`mixedForm_add_left`, …) and in each
  direction (`mixedForm_add_dir`, `mixedForm_smul_dir`), `mixedForm_zero`, and the matrix form
  `mixedForm_eq_dotProduct_mulVec`, `mulVec_mixedForm`, `isSymm_mixedForm` (the interface
  with `Parking.PerronStep`);
- `mixedForm_append_eq_prod`: derivatives along a block `vs` of directions can be applied to
  `f` first;
- homogeneity: `isHomogeneous_dirDeriv`, `isHomogeneous_prod_dirDeriv`;
- powers of one direction: `eval_dirDeriv_self` (Euler) and `eval_zero_dirDeriv_pow`
  (`D_w^p h = p! h(w)`);
- positivity: `prod_dirDeriv_ne_zero`, `eval_zero_prod_dirDeriv_pos`, `mixedForm_pos`,
  `mixedForm_nonneg`, `mixedForm_single_single_pos_iff`, `mixedForm_single_pos_iff`;
- repeated directions: with `g = D_{v₁} ⋯ D_{v_r} f` homogeneous of degree `e` and `e - 2`
  copies of `w`, `B(w, w) = e! g(w)`, `B(w, y) = (e - 1)! D_y g(w)` and
  `B(y, y) = (e - 2)! D_y² g(w)` (`mixedForm_append_replicate_self_self`,
  `mixedForm_append_replicate_self_left`, `mixedForm_append_replicate_diag`);
- continuity in the directions: `continuous_mixedForm`, for directions depending
  continuously on a parameter, and its corollary `tendsto_mixedForm_add_smul`, the form used
  by the limit `v_i + ε • 1 → v_i` in `Parking.CLCCriterion`.
-/

public section

open MvPolynomial Filter Topology Matrix

namespace Parking

/-- The mixed form `B_f[us](x, y) = D_x D_y D_{u₁} ⋯ D_{u_r} f`, read at `0`. For `f`
homogeneous of degree `r + 2` the polynomial differentiated is a constant. -/
@[expose] noncomputable def mixedForm {d : ℕ} (f : MvPolynomial (Fin d) ℝ)
    (us : List (Fin d → ℝ)) (x y : Fin d → ℝ) : ℝ :=
  eval 0 (dirDeriv x (dirDeriv y ((us.map dirDeriv).prod f)))

variable {d : ℕ}

/-! ### Directional derivatives -/

/-- The value at `0` of a polynomial is its constant coefficient. -/
theorem eval_zero_eq_coeff_zero (p : MvPolynomial (Fin d) ℝ) : eval 0 p = p.coeff 0 := by
  rw [eval_zero, constantCoeff_eq]

/-- The coefficients of a directional derivative. -/
theorem coeff_dirDeriv (v : Fin d → ℝ) (h : MvPolynomial (Fin d) ℝ) (n : Fin d →₀ ℕ) :
    (dirDeriv v h).coeff n = ∑ i, v i * (h.coeff (n + Finsupp.single i 1) * (n i + 1)) := by
  rw [dirDeriv_apply, coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, coeff_pderiv, smul_eq_mul]

/-- A partial derivative of a polynomial with nonnegative coefficients has nonnegative
coefficients. -/
theorem coeff_pderiv_nonneg {h : MvPolynomial (Fin d) ℝ} (hh : ∀ n, 0 ≤ h.coeff n) (k : Fin d)
    (n : Fin d →₀ ℕ) : 0 ≤ (pderiv k h).coeff n := by
  rw [coeff_pderiv]
  exact mul_nonneg (hh _) (by positivity)

/-- `D_v` is additive in the direction `v`. -/
theorem dirDeriv_add (v w : Fin d → ℝ) : dirDeriv (v + w) = dirDeriv v + dirDeriv w := by
  refine LinearMap.ext fun h => ?_
  simp only [LinearMap.add_apply, dirDeriv_apply, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- `D_v` is homogeneous in the direction `v`. -/
theorem dirDeriv_smul (c : ℝ) (v : Fin d → ℝ) : dirDeriv (c • v) = c • dirDeriv v := by
  refine LinearMap.ext fun h => ?_
  simp only [LinearMap.smul_apply, dirDeriv_apply, Pi.smul_apply, smul_eq_mul, mul_smul,
    Finset.smul_sum]

/-- Partial derivatives commute. -/
theorem pderiv_comm (i j : Fin d) (h : MvPolynomial (Fin d) ℝ) :
    pderiv i (pderiv j h) = pderiv j (pderiv i h) := by
  ext n
  simp only [coeff_pderiv, Finsupp.add_apply]
  rw [add_right_comm n (Finsupp.single i 1)]
  by_cases hij : i = j
  · subst hij
    rfl
  · simp only [Finsupp.single_apply, hij, Ne.symm hij, ↓reduceIte, add_zero]
    ring

/-- Directional derivatives commute. -/
theorem dirDeriv_comm (f : MvPolynomial (Fin d) ℝ) (v w : Fin d → ℝ) :
    dirDeriv v (dirDeriv w f) = dirDeriv w (dirDeriv v f) := by
  simp only [dirDeriv_apply, map_sum, Derivation.map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_comm, smul_comm]

/-- Directional derivatives commute, as elements of `Module.End`. -/
theorem commute_dirDeriv (v w : Fin d → ℝ) : Commute (dirDeriv v) (dirDeriv w) :=
  LinearMap.ext fun f => dirDeriv_comm f v w

/-- A directional derivative commutes with a product of directional derivatives. -/
theorem commute_dirDeriv_prod (v : Fin d → ℝ) (us : List (Fin d → ℝ)) :
    Commute (dirDeriv v) (us.map dirDeriv).prod :=
  Commute.list_prod_right _ _ fun _ hx => by
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
    exact commute_dirDeriv v u

/-- `D_v D_{u₁} ⋯ D_{u_r} f = D_{u₁} ⋯ D_{u_r} D_v f`. -/
theorem dirDeriv_prod_apply (v : Fin d → ℝ) (us : List (Fin d → ℝ))
    (f : MvPolynomial (Fin d) ℝ) :
    dirDeriv v ((us.map dirDeriv).prod f) = (us.map dirDeriv).prod (dirDeriv v f) :=
  LinearMap.congr_fun (commute_dirDeriv_prod v us).eq f

/-- The product of the directional derivatives along a list does not depend on the order of
the list. -/
theorem prod_map_dirDeriv_perm {us us' : List (Fin d → ℝ)} (h : us.Perm us') :
    (us.map dirDeriv).prod = (us'.map dirDeriv).prod :=
  (h.map dirDeriv).prod_eq'
    (List.pairwise_map.2 (List.pairwise_of_forall fun v w => commute_dirDeriv v w))

/-! ### Homogeneity -/

/-- A directional derivative lowers the degree of a homogeneous polynomial by one. -/
theorem isHomogeneous_dirDeriv {h : MvPolynomial (Fin d) ℝ} {p : ℕ} (hh : h.IsHomogeneous p)
    (v : Fin d → ℝ) : (dirDeriv v h).IsHomogeneous (p - 1) := by
  rw [dirDeriv_apply]
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  rw [smul_eq_C_mul]
  exact hh.pderiv.C_mul _

/-- An iterated directional derivative `D_{v₁} ⋯ D_{v_r} h` of a homogeneous polynomial of
degree `p` is homogeneous of degree `p - r` (truncated subtraction: it vanishes if
`r > p`). -/
theorem isHomogeneous_prod_dirDeriv {h : MvPolynomial (Fin d) ℝ} {p : ℕ}
    (hh : h.IsHomogeneous p) (vs : List (Fin d → ℝ)) :
    ((vs.map dirDeriv).prod h).IsHomogeneous (p - vs.length) := by
  induction vs with
  | nil => simpa using hh
  | cons v vs ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, ← Nat.sub_sub]
    exact isHomogeneous_dirDeriv ih v

/-! ### Powers of one direction -/

/-- Euler's identity along a direction: `(D_w h)(w) = p h(w)` for `h` homogeneous of degree
`p`. -/
theorem eval_dirDeriv_self {h : MvPolynomial (Fin d) ℝ} {p : ℕ} (hh : h.IsHomogeneous p)
    (w : Fin d → ℝ) : eval w (dirDeriv w h) = p * eval w h := by
  have hE := congrArg (eval w) hh.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at hE
  rw [dirDeriv_apply, map_sum]
  simp only [smul_eval]
  exact hE

/-- `D_w^m h = m! h(w)` for `h` homogeneous of degree `m` (by induction on `m` and Euler's
identity). -/
theorem eval_zero_dirDeriv_pow {m : ℕ} (h : MvPolynomial (Fin d) ℝ) (w : Fin d → ℝ)
    (hh : h.IsHomogeneous m) : eval 0 ((dirDeriv w ^ m) h) = (m.factorial : ℝ) * eval w h := by
  induction m generalizing h with
  | zero =>
    have hC : h = C (h.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hh)
    rw [pow_zero, Module.End.one_apply, hC, eval_C, eval_C, Nat.factorial_zero, Nat.cast_one,
      one_mul]
  | succ m ih =>
    have hw : (dirDeriv w h).IsHomogeneous m := by
      simpa using isHomogeneous_dirDeriv hh w
    rw [pow_succ, Module.End.mul_apply, ih _ hw, eval_dirDeriv_self hh, Nat.factorial_succ]
    push_cast
    ring

/-! ### Positivity -/

/-- Iterated derivatives in positive directions of a nonzero homogeneous polynomial with
nonnegative coefficients do not vanish as long as their number is at most the degree. -/
theorem prod_dirDeriv_ne_zero {g : MvPolynomial (Fin d) ℝ} {p : ℕ} (hg : g.IsHomogeneous p)
    (hcoeff : ∀ n, 0 ≤ g.coeff n) (hg0 : g ≠ 0) {vs : List (Fin d → ℝ)}
    (hvs : ∀ v ∈ vs, ∀ i, 0 < v i) (hlen : vs.length ≤ p) : (vs.map dirDeriv).prod g ≠ 0 := by
  induction vs with
  | nil => simpa using hg0
  | cons v vs ih =>
    have hvs' : ∀ u ∈ vs, ∀ i, 0 < u i := fun u hu => hvs u (List.mem_cons_of_mem _ hu)
    have hlen' : vs.length < p := by
      rw [List.length_cons] at hlen
      omega
    have hne := ih hvs' hlen'.le
    have hnn := coeff_prod_dirDeriv_nonneg hcoeff (vs := vs) fun u hu i => (hvs' u hu i).le
    have hv : v ∈ posOrthant d := hvs v (by simp)
    have hpos := eval_pos_of_coeff_nonneg hnn hne hv
    have hE := eval_dirDeriv_self (isHomogeneous_prod_dirDeriv hg vs) v
    have hp : (0 : ℝ) < ((p - vs.length : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hlen'
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    intro h0
    rw [h0, map_zero] at hE
    exact (mul_pos hp hpos).ne hE

/-- **Positivity.** For `g ≠ 0` homogeneous of degree `p` with nonnegative coefficients and
positive directions `v₁, …, v_p`, the constant `D_{v₁} ⋯ D_{v_p} g` is positive. -/
theorem eval_zero_prod_dirDeriv_pos {g : MvPolynomial (Fin d) ℝ} {p : ℕ}
    (hg : g.IsHomogeneous p) (hcoeff : ∀ n, 0 ≤ g.coeff n) (hg0 : g ≠ 0)
    {vs : List (Fin d → ℝ)} (hvs : ∀ v ∈ vs, ∀ i, 0 < v i) (hlen : vs.length = p) :
    0 < eval 0 ((vs.map dirDeriv).prod g) := by
  have hne := prod_dirDeriv_ne_zero hg hcoeff hg0 hvs hlen.le
  have hhom : ((vs.map dirDeriv).prod g).IsHomogeneous 0 := by
    simpa [hlen] using isHomogeneous_prod_dirDeriv hg vs
  have hnn := coeff_prod_dirDeriv_nonneg hcoeff (vs := vs) fun u hu i => (hvs u hu i).le
  have hC := totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hhom)
  rw [hC, eval_C]
  refine lt_of_le_of_ne (hnn 0) fun h0 => hne ?_
  rw [hC, ← h0, C_0]

/-- Positivity, as an equivalence: for positive directions `v₁, …, v_p` and `g` homogeneous
of degree `p` with nonnegative coefficients, `D_{v₁} ⋯ D_{v_p} g > 0` if and only if
`g ≠ 0`. -/
theorem eval_zero_prod_dirDeriv_pos_iff {g : MvPolynomial (Fin d) ℝ} {p : ℕ}
    (hg : g.IsHomogeneous p) (hcoeff : ∀ n, 0 ≤ g.coeff n) {vs : List (Fin d → ℝ)}
    (hvs : ∀ v ∈ vs, ∀ i, 0 < v i) (hlen : vs.length = p) :
    0 < eval 0 ((vs.map dirDeriv).prod g) ↔ g ≠ 0 := by
  refine ⟨fun h hg0 => ?_, fun hg0 => eval_zero_prod_dirDeriv_pos hg hcoeff hg0 hvs hlen⟩
  rw [hg0, map_zero, map_zero] at h
  exact lt_irrefl 0 h

/-! ### The mixed form: basic identities -/

/-- The mixed form as the value at `0` of the iterated derivative along `x :: y :: us`. -/
theorem mixedForm_eq_eval_prod (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (x y : Fin d → ℝ) : mixedForm f us x y = eval 0 (((x :: y :: us).map dirDeriv).prod f) := by
  simp only [mixedForm, List.map_cons, List.prod_cons, Module.End.mul_apply]

/-- The mixed form with the derivatives in `x` and `y` applied first. -/
theorem mixedForm_eq_eval_prod_dirDeriv (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (x y : Fin d → ℝ) :
    mixedForm f us x y = eval 0 ((us.map dirDeriv).prod (dirDeriv x (dirDeriv y f))) := by
  rw [mixedForm, dirDeriv_prod_apply y us f, dirDeriv_prod_apply x us]

/-- The mixed form with no direction. -/
theorem mixedForm_nil (f : MvPolynomial (Fin d) ℝ) (x y : Fin d → ℝ) :
    mixedForm f [] x y = eval 0 (dirDeriv x (dirDeriv y f)) := by
  simp only [mixedForm, List.map_nil, List.prod_nil, Module.End.one_apply]

/-- The mixed form of the zero polynomial vanishes. -/
theorem mixedForm_zero (us : List (Fin d → ℝ)) (x y : Fin d → ℝ) :
    mixedForm (0 : MvPolynomial (Fin d) ℝ) us x y = 0 := by
  simp only [mixedForm, map_zero]

/-- **Symmetry** of the mixed form in `x` and `y`. -/
theorem mixedForm_comm (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (x y : Fin d → ℝ) : mixedForm f us x y = mixedForm f us y x := by
  rw [mixedForm, mixedForm, dirDeriv_comm]

/-- **Symmetry in the directions**: the mixed form is invariant under permutation of `us`. -/
theorem mixedForm_perm (f : MvPolynomial (Fin d) ℝ) {us us' : List (Fin d → ℝ)}
    (h : us.Perm us') (x y : Fin d → ℝ) : mixedForm f us x y = mixedForm f us' x y := by
  rw [mixedForm, mixedForm, prod_map_dirDeriv_perm h]

/-- Derivatives along a block of directions can be applied to `f` first. -/
theorem mixedForm_append_eq_prod (f : MvPolynomial (Fin d) ℝ) (vs us : List (Fin d → ℝ))
    (x y : Fin d → ℝ) :
    mixedForm f (vs ++ us) x y = mixedForm ((vs.map dirDeriv).prod f) us x y := by
  rw [mixedForm_perm f List.perm_append_comm, mixedForm, mixedForm, List.map_append,
    List.prod_append, Module.End.mul_apply]

/-- **Euler decomposition along the last direction**: `B_f[us, w] = ∑_k w_k B_{∂_k f}[us]`.
No commutation is needed. -/
theorem mixedForm_append (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (w x y : Fin d → ℝ) :
    mixedForm f (us ++ [w]) x y = ∑ k, w k * mixedForm (pderiv k f) us x y := by
  rw [mixedForm, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
    Module.End.mul_apply, dirDeriv_apply w f]
  simp only [map_sum, map_smul, smul_eval, mixedForm]

/-- `B_{∂_k f}[us](x, w) = B_f[us, w](x, e_k)`, by commutation of the derivatives. -/
theorem mixedForm_pderiv (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (k : Fin d) (w x : Fin d → ℝ) :
    mixedForm (pderiv k f) us x w = mixedForm f (us ++ [w]) x (Pi.single k 1) := by
  rw [mixedForm_eq_eval_prod_dirDeriv, mixedForm_eq_eval_prod_dirDeriv, List.map_append,
    List.prod_append, List.map_singleton, List.prod_singleton, Module.End.mul_apply,
    dirDeriv_comm (pderiv k f) x w, dirDeriv_single]
  rfl

/-! ### Linearity -/

/-- Additivity in the first argument. -/
theorem mixedForm_add_left (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (x x' y : Fin d → ℝ) :
    mixedForm f us (x + x') y = mixedForm f us x y + mixedForm f us x' y := by
  simp only [mixedForm, dirDeriv_add, LinearMap.add_apply, map_add]

/-- Homogeneity in the first argument. -/
theorem mixedForm_smul_left (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ)) (c : ℝ)
    (x y : Fin d → ℝ) : mixedForm f us (c • x) y = c * mixedForm f us x y := by
  simp only [mixedForm, dirDeriv_smul, LinearMap.smul_apply, smul_eval]

/-- Additivity in the second argument. -/
theorem mixedForm_add_right (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (x y y' : Fin d → ℝ) :
    mixedForm f us x (y + y') = mixedForm f us x y + mixedForm f us x y' := by
  rw [mixedForm_comm, mixedForm_add_left, mixedForm_comm f us y, mixedForm_comm f us y']

/-- Homogeneity in the second argument. -/
theorem mixedForm_smul_right (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ)) (c : ℝ)
    (x y : Fin d → ℝ) : mixedForm f us x (c • y) = c * mixedForm f us x y := by
  rw [mixedForm_comm, mixedForm_smul_left, mixedForm_comm f us y]

/-- Additivity in each direction of `us` (any position, by `us₁ ++ u :: us₂`). -/
theorem mixedForm_add_dir (f : MvPolynomial (Fin d) ℝ) (us₁ us₂ : List (Fin d → ℝ))
    (u u' x y : Fin d → ℝ) :
    mixedForm f (us₁ ++ (u + u') :: us₂) x y =
      mixedForm f (us₁ ++ u :: us₂) x y + mixedForm f (us₁ ++ u' :: us₂) x y := by
  simp only [mixedForm, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    dirDeriv_add, add_mul, mul_add, LinearMap.add_apply, map_add]

/-- Homogeneity in each direction of `us` (any position, by `us₁ ++ u :: us₂`). -/
theorem mixedForm_smul_dir (f : MvPolynomial (Fin d) ℝ) (us₁ us₂ : List (Fin d → ℝ)) (c : ℝ)
    (u x y : Fin d → ℝ) :
    mixedForm f (us₁ ++ (c • u) :: us₂) x y = c * mixedForm f (us₁ ++ u :: us₂) x y := by
  simp only [mixedForm, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    dirDeriv_smul, smul_mul_assoc, mul_smul_comm, LinearMap.smul_apply, map_smul, smul_eval]

/-- Expansion in the coordinates of `x` and `y`. -/
theorem mixedForm_eq_sum (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (x y : Fin d → ℝ) :
    mixedForm f us x y =
      ∑ k, ∑ l, x k * y l * mixedForm f us (Pi.single k 1) (Pi.single l 1) := by
  have hkl : ∀ k l, mixedForm f us (Pi.single k 1) (Pi.single l 1) =
      eval 0 (pderiv k (pderiv l ((us.map dirDeriv).prod f))) := by
    intro k l
    rw [mixedForm, dirDeriv_single, dirDeriv_single]
    rfl
  rw [mixedForm, dirDeriv_apply x, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eval, dirDeriv_apply y, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hkl, Derivation.map_smul, smul_eval]
  ring

/-- **Matrix form**: `B(x, y) = x ⬝ᵥ (A *ᵥ y)` with `A k l = B(e_k, e_l)`. -/
theorem mixedForm_eq_dotProduct_mulVec (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (x y : Fin d → ℝ) :
    mixedForm f us x y =
      x ⬝ᵥ (Matrix.of (fun k l => mixedForm f us (Pi.single k 1) (Pi.single l 1)) *ᵥ y) := by
  rw [mixedForm_eq_sum]
  simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The entries of `A *ᵥ y`, for the matrix `A k l = B(e_k, e_l)` of the mixed form. -/
theorem mulVec_mixedForm (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ))
    (y : Fin d → ℝ) (k : Fin d) :
    (Matrix.of (fun k l => mixedForm f us (Pi.single k 1) (Pi.single l 1)) *ᵥ y) k =
      mixedForm f us (Pi.single k 1) y := by
  rw [mixedForm_eq_dotProduct_mulVec f us (Pi.single k 1) y, single_dotProduct, one_mul]

/-- The matrix `A k l = B(e_k, e_l)` of the mixed form is symmetric. -/
theorem isSymm_mixedForm (f : MvPolynomial (Fin d) ℝ) (us : List (Fin d → ℝ)) :
    (Matrix.of fun k l => mixedForm f us (Pi.single k 1) (Pi.single l 1)).IsSymm :=
  IsSymm.ext fun k l => by
    simp only [Matrix.of_apply]
    exact mixedForm_comm f us _ _

/-! ### Positivity of the mixed form -/

/-- The mixed form of a polynomial with nonnegative coefficients is nonnegative on
nonnegative arguments and directions. -/
theorem mixedForm_nonneg {f : MvPolynomial (Fin d) ℝ} (hcoeff : ∀ n, 0 ≤ f.coeff n)
    {us : List (Fin d → ℝ)} (hus : ∀ u ∈ us, ∀ i, 0 ≤ u i) {x y : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) : 0 ≤ mixedForm f us x y := by
  rw [mixedForm_eq_eval_prod, eval_zero_eq_coeff_zero]
  refine coeff_prod_dirDeriv_nonneg hcoeff (fun v hv => ?_) 0
  simp only [List.mem_cons] at hv
  rcases hv with rfl | rfl | hv
  · exact hx
  · exact hy
  · exact hus v hv

/-- The mixed form of a nonzero homogeneous polynomial of degree `us.length + 2` with
nonnegative coefficients is positive on positive arguments and directions. -/
theorem mixedForm_pos {f : MvPolynomial (Fin d) ℝ} {m : ℕ} (hf : f.IsHomogeneous m)
    (hcoeff : ∀ n, 0 ≤ f.coeff n) (hf0 : f ≠ 0) {us : List (Fin d → ℝ)}
    (hus : ∀ u ∈ us, ∀ i, 0 < u i) (hlen : us.length + 2 = m) {x y : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) : 0 < mixedForm f us x y := by
  rw [mixedForm_eq_eval_prod]
  refine eval_zero_prod_dirDeriv_pos hf hcoeff hf0 (fun v hv => ?_) ?_
  · simp only [List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact hx
    · exact hy
    · exact hus v hv
  · simp only [List.length_cons]
    omega

/-- For positive directions, `B(e_k, e_l) > 0` if and only if `∂_k ∂_l f ≠ 0`. -/
theorem mixedForm_single_single_pos_iff {f : MvPolynomial (Fin d) ℝ} {m : ℕ}
    (hf : f.IsHomogeneous m) (hcoeff : ∀ n, 0 ≤ f.coeff n) {us : List (Fin d → ℝ)}
    (hus : ∀ u ∈ us, ∀ i, 0 < u i) (hlen : us.length + 2 = m) (k l : Fin d) :
    0 < mixedForm f us (Pi.single k 1) (Pi.single l 1) ↔ pderiv k (pderiv l f) ≠ 0 := by
  rw [mixedForm_eq_eval_prod_dirDeriv, dirDeriv_single, dirDeriv_single]
  exact eval_zero_prod_dirDeriv_pos_iff hf.pderiv.pderiv
    (coeff_pderiv_nonneg (coeff_pderiv_nonneg hcoeff l) k) hus (by omega)

/-- For positive directions and positive `w`, `B(w, e_k) > 0` if and only if
`∂_k f ≠ 0`. -/
theorem mixedForm_single_pos_iff {f : MvPolynomial (Fin d) ℝ} {m : ℕ}
    (hf : f.IsHomogeneous m) (hcoeff : ∀ n, 0 ≤ f.coeff n) {us : List (Fin d → ℝ)}
    (hus : ∀ u ∈ us, ∀ i, 0 < u i) (hlen : us.length + 2 = m) {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) (k : Fin d) :
    0 < mixedForm f us w (Pi.single k 1) ↔ pderiv k f ≠ 0 := by
  have heq : mixedForm f us w (Pi.single k 1) =
      eval 0 (((us ++ [w]).map dirDeriv).prod (pderiv k f)) := by
    rw [mixedForm_eq_eval_prod_dirDeriv, dirDeriv_single, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, Module.End.mul_apply]
    rfl
  rw [heq]
  refine eval_zero_prod_dirDeriv_pos_iff hf.pderiv (coeff_pderiv_nonneg hcoeff k)
    (fun v hv => ?_) ?_
  · rcases List.mem_append.1 hv with hv | hv
    · exact hus v hv
    · rw [List.mem_singleton.1 hv]
      exact hw
  · rw [List.length_append, List.length_singleton]
    omega

/-! ### Repeated directions: one direction repeated -/

/-- With `e - 2` copies of `w`, `B_g[w, …, w](x, y) = (e - 2)! D_x D_y g(w)` for `g`
homogeneous of degree `e`. -/
theorem mixedForm_replicate {g : MvPolynomial (Fin d) ℝ} {e : ℕ} (hg : g.IsHomogeneous e)
    (w x y : Fin d → ℝ) :
    mixedForm g (List.replicate (e - 2) w) x y =
      ((e - 2).factorial : ℝ) * eval w (dirDeriv x (dirDeriv y g)) := by
  have hxy : (dirDeriv x (dirDeriv y g)).IsHomogeneous (e - 2) := by
    have := isHomogeneous_dirDeriv (isHomogeneous_dirDeriv hg y) x
    rwa [Nat.sub_sub] at this
  rw [mixedForm_eq_eval_prod_dirDeriv, List.map_replicate, List.prod_replicate]
  exact eval_zero_dirDeriv_pow _ w hxy

/-- `B_g[w, …, w](w, y) = (e - 1)! D_y g(w)`, with `e - 2` copies of `w`, for `g`
homogeneous of degree `e ≥ 2`. -/
theorem mixedForm_replicate_self_left {g : MvPolynomial (Fin d) ℝ} {e : ℕ}
    (hg : g.IsHomogeneous e) (he : 2 ≤ e) (w y : Fin d → ℝ) :
    mixedForm g (List.replicate (e - 2) w) w y =
      ((e - 1).factorial : ℝ) * eval w (dirDeriv y g) := by
  rw [mixedForm_replicate hg, eval_dirDeriv_self (isHomogeneous_dirDeriv hg y)]
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  rw [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega, Nat.factorial_succ]
  push_cast
  ring

/-- `B_g[w, …, w](w, w) = e! g(w)`, with `e - 2` copies of `w`, for `g` homogeneous of
degree `e ≥ 2`. -/
theorem mixedForm_replicate_self_self {g : MvPolynomial (Fin d) ℝ} {e : ℕ}
    (hg : g.IsHomogeneous e) (he : 2 ≤ e) (w : Fin d → ℝ) :
    mixedForm g (List.replicate (e - 2) w) w w = (e.factorial : ℝ) * eval w g := by
  rw [mixedForm_replicate_self_left hg he, eval_dirDeriv_self hg]
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega, Nat.factorial_succ]
  push_cast
  ring

/-- Repeated directions, general form: for `g = D_{v₁} ⋯ D_{v_r} f` homogeneous of degree `e`,
`B_f[v₁, …, v_r, w, …, w](x, y) = (e - 2)! D_x D_y g(w)`, with `e - 2` copies of `w`. -/
theorem mixedForm_append_replicate {f : MvPolynomial (Fin d) ℝ} {vs : List (Fin d → ℝ)}
    {e : ℕ} (hg : ((vs.map dirDeriv).prod f).IsHomogeneous e) (w x y : Fin d → ℝ) :
    mixedForm f (vs ++ List.replicate (e - 2) w) x y =
      ((e - 2).factorial : ℝ) * eval w (dirDeriv x (dirDeriv y ((vs.map dirDeriv).prod f))) := by
  rw [mixedForm_append_eq_prod]
  exact mixedForm_replicate hg w x y

/-- Repeated directions: `B(w, w) = e! g(w)`, for `g = D_{v₁} ⋯ D_{v_r} f` homogeneous of
degree `e ≥ 2` and `B = B_f[v₁, …, v_r, w, …, w]` with `e - 2` copies of `w`. -/
theorem mixedForm_append_replicate_self_self {f : MvPolynomial (Fin d) ℝ}
    {vs : List (Fin d → ℝ)} {e : ℕ} (hg : ((vs.map dirDeriv).prod f).IsHomogeneous e)
    (he : 2 ≤ e) (w : Fin d → ℝ) :
    mixedForm f (vs ++ List.replicate (e - 2) w) w w =
      (e.factorial : ℝ) * eval w ((vs.map dirDeriv).prod f) := by
  rw [mixedForm_append_eq_prod]
  exact mixedForm_replicate_self_self hg he w

/-- Repeated directions: `B(w, y) = (e - 1)! D_y g(w)`, for `g = D_{v₁} ⋯ D_{v_r} f`
homogeneous of degree `e ≥ 2` and `B = B_f[v₁, …, v_r, w, …, w]` with `e - 2` copies
of `w`. -/
theorem mixedForm_append_replicate_self_left {f : MvPolynomial (Fin d) ℝ}
    {vs : List (Fin d → ℝ)} {e : ℕ} (hg : ((vs.map dirDeriv).prod f).IsHomogeneous e)
    (he : 2 ≤ e) (w y : Fin d → ℝ) :
    mixedForm f (vs ++ List.replicate (e - 2) w) w y =
      ((e - 1).factorial : ℝ) * eval w (dirDeriv y ((vs.map dirDeriv).prod f)) := by
  rw [mixedForm_append_eq_prod]
  exact mixedForm_replicate_self_left hg he w y

/-- Repeated directions: `B(y, y) = (e - 2)! D_y² g(w)`, for `g = D_{v₁} ⋯ D_{v_r} f`
homogeneous of degree `e` and `B = B_f[v₁, …, v_r, w, …, w]` with `e - 2` copies of `w`. -/
theorem mixedForm_append_replicate_diag {f : MvPolynomial (Fin d) ℝ}
    {vs : List (Fin d → ℝ)} {e : ℕ} (hg : ((vs.map dirDeriv).prod f).IsHomogeneous e)
    (w y : Fin d → ℝ) :
    mixedForm f (vs ++ List.replicate (e - 2) w) y y =
      ((e - 2).factorial : ℝ) * eval w (dirDeriv y (dirDeriv y ((vs.map dirDeriv).prod f))) :=
  mixedForm_append_replicate hg w y y

/-! ### Continuity in the directions -/

/-- Each coefficient of `D_{u₁(t)} ⋯ D_{u_r(t)} f` depends continuously on `t` when the
directions do. -/
theorem continuous_coeff_prod_dirDeriv {T : Type*} [TopologicalSpace T]
    (f : MvPolynomial (Fin d) ℝ) {us : List (T → Fin d → ℝ)} (hus : ∀ u ∈ us, Continuous u)
    (n : Fin d →₀ ℕ) :
    Continuous fun t => (((us.map fun u => u t).map dirDeriv).prod f).coeff n := by
  induction us generalizing n with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply]
    exact continuous_const
  | cons u us ih =>
    have hu : Continuous u := hus u (by simp)
    have ih' := ih (fun v hv => hus v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, coeff_dirDeriv]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hu).mul ((ih' _).mul continuous_const)

/-- **Continuity in the directions.** If the directions `us` and the arguments `x, y`
depend continuously on a parameter `t`, so does the mixed form. -/
theorem continuous_mixedForm {T : Type*} [TopologicalSpace T] (f : MvPolynomial (Fin d) ℝ)
    {us : List (T → Fin d → ℝ)} (hus : ∀ u ∈ us, Continuous u) {x y : T → Fin d → ℝ}
    (hx : Continuous x) (hy : Continuous y) :
    Continuous fun t => mixedForm f (us.map fun u => u t) (x t) (y t) := by
  have h := continuous_coeff_prod_dirDeriv f (us := x :: y :: us) (fun v hv => by
    simp only [List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact hx
    · exact hy
    · exact hus v hv) 0
  simp only [mixedForm_eq_eval_prod, eval_zero_eq_coeff_zero]
  exact h

/-- **Continuity in the directions.** Perturbing the directions `vs` to `v + ε • c` changes the
mixed form continuously: as `ε → 0`, `B_f[(v + ε c)_{v ∈ vs}, us](x, y) → B_f[vs, us](x, y)`.
Use it with `c = 1` and `Tendsto.mono_left nhdsWithin_le_nhds` for `ε → 0⁺`. -/
theorem tendsto_mixedForm_add_smul (f : MvPolynomial (Fin d) ℝ) (vs us : List (Fin d → ℝ))
    (c x y : Fin d → ℝ) :
    Tendsto (fun ε : ℝ => mixedForm f ((vs.map fun v => v + ε • c) ++ us) x y) (𝓝 0)
      (𝓝 (mixedForm f (vs ++ us) x y)) := by
  have hcont := continuous_mixedForm f
    (us := (vs.map fun v (ε : ℝ) => v + ε • c) ++ us.map fun u (_ : ℝ) => u)
    (fun u hu => by
      rcases List.mem_append.1 hu with hu | hu
      · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
        exact continuous_const.add (continuous_id.smul continuous_const)
      · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
        exact continuous_const)
    (x := fun _ => x) (y := fun _ => y) continuous_const continuous_const
  have key : ∀ ε : ℝ,
      ((vs.map fun v (ε : ℝ) => v + ε • c) ++ us.map fun u (_ : ℝ) => u).map (fun u => u ε) =
        (vs.map fun v => v + ε • c) ++ us := by
    intro ε
    simp [List.map_append, List.map_map, Function.comp_def]
  simp only [key] at hcont
  have h0 : (vs.map fun v => v + (0 : ℝ) • c) ++ us = vs ++ us := by simp
  have := hcont.tendsto 0
  rwa [h0] at this

end Parking
