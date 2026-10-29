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

public import Parking.MixedForm
public import Parking.RevCauchySchwarz
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Mixed-Lorentzian polynomials are completely log-concave

Let `f` be homogeneous
of degree `m` with nonnegative coefficients, and assume that the mixed form
`B_f[u₁, …, u_{m-2}]` satisfies the reverse Cauchy–Schwarz inequality `RevCS` for all positive
directions `u_i`. Then `f` is completely log-concave (`completelyLogConcave_of_revCS`).

For nonnegative directions `v₁, …, v_r` and `g = D_{v₁} ⋯ D_{v_r} f ≠ 0`, homogeneous of degree
`e`, the proof shows `g(w) D_y² g(w) ≤ (D_y g(w))²` for all `w > 0` and all `y`:

- if `e ≤ 1`, then `D_y² g = 0`;
- if `e ≥ 2`, with `B = B_f[v₁, …, v_r, w, …, w]` (`e - 2` copies of `w`), one has
  `B(w, w) = e! g(w)`, `B(w, y) = (e - 1)! D_y g(w)` and `B(y, y) = (e - 2)! D_y² g(w)`
  (`Parking.MixedForm`), and `RevCS B` at `w` gives `e g D_y² g ≤ (e - 1) (D_y g)²`. This is the
  computation in the proof of [BH20, Proposition 2.33] (Brändén–Huh, *Lorentzian polynomials*,
  arXiv:1902.03719), done directly from `RevCS`. The hypothesis only gives `RevCS` for
  positive directions; the directions `v_i + ε 1` are positive and `RevCS` passes to the limit
  `ε → 0⁺` (`RevCS.of_tendsto`, `tendsto_mixedForm_add_smul`).

The inequality says that `t ↦ log g(z + t y)` has a nonpositive second derivative, hence
`log g` is concave along every segment of the positive orthant, hence on the orthant
(`concaveOn_log_eval_of_sq_le`).

The positive-direction hypothesis is the conclusion of the induction of Brändén–Leake,
*Lorentzian polynomials on cones*, arXiv:2304.13203v2, Theorem 2.10 and Lemma 2.8, for the cone
`ℝ^d_{>0}` (`Parking.PerronStep` and `Parking.SupportGenFunCLC`).

Main results:

- `hasDerivAt_eval_add_smul`: the derivative of `t ↦ g(z + t y)` is `t ↦ D_y g(z + t y)`;
- `concaveOn_log_eval_of_sq_le`: the concavity criterion on the positive orthant;
- `dirDeriv_dirDeriv_eq_zero`: the cases of degree `0` and `1`;
- `revCS_mixedForm_append_of_nonneg`: the limit to nonnegative directions;
- `eval_mul_eval_dirDeriv_dirDeriv_le`: the case of degree `≥ 2`;
- `completelyLogConcave_of_revCS`: mixed-Lorentzian implies completely log-concave.
-/

public section

open MvPolynomial Filter Topology Set

namespace Parking

variable {d : ℕ}

/-! ### Derivatives along a line -/

/-- A directional derivative kills the constants. -/
theorem dirDeriv_C (v : Fin d → ℝ) (a : ℝ) : dirDeriv v (C a : MvPolynomial (Fin d) ℝ) = 0 := by
  simp [dirDeriv_apply]

/-- The product rule for `D_v (p X_i)`, after evaluation at `z`. -/
theorem eval_dirDeriv_mul_X (v z : Fin d → ℝ) (p : MvPolynomial (Fin d) ℝ) (i : Fin d) :
    eval z (dirDeriv v (p * X i)) = eval z (dirDeriv v p) * z i + eval z p * v i := by
  classical
  have hX : ∀ j, eval z (pderiv j (X i : MvPolynomial (Fin d) ℝ)) = if j = i then 1 else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [pderiv_X_of_ne (Ne.symm hj), hj]
  simp only [dirDeriv_apply, map_sum, smul_eval, pderiv_mul, map_add, map_mul, eval_X, hX,
    mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_mul, mul_comm (eval z p) (v i)]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Derivative along a line.** The derivative of `t ↦ g(z + t y)` is `t ↦ D_y g(z + t y)`. -/
theorem hasDerivAt_eval_add_smul (g : MvPolynomial (Fin d) ℝ) (z y : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => eval (z + s • y) g) (eval (z + t • y) (dirDeriv y g)) t := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa [dirDeriv_C] using hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.fun_add hq
  | mul_X p i hp =>
    rw [eval_dirDeriv_mul_X]
    have hlin : HasDerivAt (fun s : ℝ => z i + s * y i) (y i) t := by
      simpa using ((hasDerivAt_id t).mul_const (y i)).const_add (z i)
    convert hp.fun_mul hlin using 1
    funext s
    simp

/-! ### The concavity criterion -/

/-- The positive orthant is convex. -/
theorem convex_posOrthant (d : ℕ) : Convex ℝ (posOrthant d) := by
  intro x hx y hy a b ha hb hab i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hx i)) (mul_nonneg hb (hy i).le)
  · rw [zero_add] at hab
    subst hab
    simpa using hy i

/-- **Concavity criterion.** If `g > 0` on the positive orthant and
`g(z) D_y² g(z) ≤ (D_y g(z))²` for every `z > 0` and every direction `y`, then `log g` is
concave on the positive orthant: along each segment, `t ↦ log g(z + t y)` has the nonpositive
second derivative `(g D_y² g - (D_y g)²) / g²`. -/
theorem concaveOn_log_eval_of_sq_le {g : MvPolynomial (Fin d) ℝ}
    (hpos : ∀ z ∈ posOrthant d, 0 < eval z g)
    (hineq : ∀ z ∈ posOrthant d, ∀ y : Fin d → ℝ,
      eval z g * eval z (dirDeriv y (dirDeriv y g)) ≤ eval z (dirDeriv y g) ^ 2) :
    ConcaveOn ℝ (posOrthant d) fun z => Real.log (eval z g) := by
  refine ⟨convex_posOrthant d, fun x hx y hy a b ha hb hab => ?_⟩
  set v := y - x with hv
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ posOrthant d := by
    intro t ht
    have h := convex_posOrthant d hx hy (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
    convert h using 1
    rw [hv]
    module
  have hd1 : ∀ t, x + t • v ∈ posOrthant d →
      HasDerivAt (fun s : ℝ => Real.log (eval (x + s • v) g))
        (eval (x + t • v) (dirDeriv v g) / eval (x + t • v) g) t :=
    fun t ht => (hasDerivAt_eval_add_smul g x v t).log (hpos _ ht).ne'
  have hd2 : ∀ t, x + t • v ∈ posOrthant d →
      HasDerivAt (fun s : ℝ => eval (x + s • v) (dirDeriv v g) / eval (x + s • v) g)
        ((eval (x + t • v) (dirDeriv v (dirDeriv v g)) * eval (x + t • v) g -
            eval (x + t • v) (dirDeriv v g) * eval (x + t • v) (dirDeriv v g)) /
          eval (x + t • v) g ^ 2) t :=
    fun t ht => (hasDerivAt_eval_add_smul _ x v t).fun_div (hasDerivAt_eval_add_smul g x v t)
      (hpos _ ht).ne'
  have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) fun s => Real.log (eval (x + s • v) g) := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
      (f' := fun t => eval (x + t • v) (dirDeriv v g) / eval (x + t • v) g)
      (f'' := fun t => (eval (x + t • v) (dirDeriv v (dirDeriv v g)) * eval (x + t • v) g -
          eval (x + t • v) (dirDeriv v g) * eval (x + t • v) (dirDeriv v g)) /
        eval (x + t • v) g ^ 2)
      (fun t ht => (hd1 t (hseg t ht)).continuousAt.continuousWithinAt) (fun t ht => ?_)
      (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht ⊢
      exact (hd1 t (hseg t (Ioo_subset_Icc_self ht))).hasDerivWithinAt
    · rw [interior_Icc] at ht ⊢
      exact (hd2 t (hseg t (Ioo_subset_Icc_self ht))).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have h := hineq _ (hseg t (Ioo_subset_Icc_self ht)) v
      refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
      nlinarith [h]
  have h := hconc.2 (x := 0) (y := 1) ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ ha hb hab
  have ha' : a = 1 - b := by linarith
  subst ha'
  have h0 : x + (0 : ℝ) • v = x := by simp
  have h1 : x + (1 : ℝ) • v = y := by simp [hv]
  have hb' : x + ((1 - b) • (0 : ℝ) + b • (1 : ℝ)) • v = (1 - b) • x + b • y := by
    rw [hv]
    module
  simp only [h0, h1, hb'] at h
  exact h

/-! ### Degrees `0` and `1` -/

/-- A directional derivative of a homogeneous polynomial of degree `0` (a constant) is `0`. -/
theorem dirDeriv_eq_zero_of_isHomogeneous_zero {h : MvPolynomial (Fin d) ℝ}
    (hh : h.IsHomogeneous 0) (v : Fin d → ℝ) : dirDeriv v h = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hh), dirDeriv_C]

/-- **Degrees `0` and `1`.** For `h` homogeneous of degree `e ≤ 1`, `D_y² h = 0`. -/
theorem dirDeriv_dirDeriv_eq_zero {h : MvPolynomial (Fin d) ℝ} {e : ℕ} (hh : h.IsHomogeneous e)
    (he : e ≤ 1) (y : Fin d → ℝ) : dirDeriv y (dirDeriv y h) = 0 := by
  have h1 := isHomogeneous_dirDeriv hh y
  rw [show e - 1 = 0 by omega] at h1
  exact dirDeriv_eq_zero_of_isHomogeneous_zero h1 y

/-! ### Degree `≥ 2` -/

/-- **The limit to nonnegative directions.** If `RevCS (mixedForm f us)` holds for every list
`us` of positive directions of length `m - 2`, then it holds for `vs ++ us` with `vs`
nonnegative and `us` positive: `RevCS` passes from `v + ε 1` to `v` as `ε → 0⁺`. -/
theorem revCS_mixedForm_append_of_nonneg {f : MvPolynomial (Fin d) ℝ} {m : ℕ}
    (h : ∀ us : List (Fin d → ℝ), us.length + 2 = m → (∀ u ∈ us, ∀ i, 0 < u i) →
      RevCS (mixedForm f us))
    {vs us : List (Fin d → ℝ)} (hvs : ∀ v ∈ vs, ∀ i, 0 ≤ v i) (hus : ∀ u ∈ us, ∀ i, 0 < u i)
    (hlen : vs.length + us.length + 2 = m) : RevCS (mixedForm f (vs ++ us)) := by
  refine RevCS.of_tendsto (l := 𝓝[>] (0 : ℝ))
    (B := fun ε => mixedForm f ((vs.map fun v => v + ε • fun _ => (1 : ℝ)) ++ us))
    (fun x y => (tendsto_mixedForm_add_smul f vs us _ x y).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  refine h _ (by rw [List.length_append, List.length_map]; omega) fun u hu i => ?_
  rcases List.mem_append.1 hu with hu | hu
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    exact add_pos_of_nonneg_of_pos (hvs v hv i) hε
  · exact hus u hu i

/-- **Degree `≥ 2`.** Let `g = D_{v₁} ⋯ D_{v_r} f` be homogeneous of degree `e ≥ 2` with
`g(w) > 0`. If `B = B_f[v₁, …, v_r, w, …, w]` (`e - 2` copies of `w`) satisfies `RevCS`, then
`g(w) D_y² g(w) ≤ (D_y g(w))²`: `RevCS` at `w` reads `e g D_y² g ≤ (e - 1) (D_y g)²`. -/
theorem eval_mul_eval_dirDeriv_dirDeriv_le {f : MvPolynomial (Fin d) ℝ} {vs : List (Fin d → ℝ)}
    {e : ℕ} (hg : ((vs.map dirDeriv).prod f).IsHomogeneous e) (he : 2 ≤ e) {w : Fin d → ℝ}
    (hpos : 0 < eval w ((vs.map dirDeriv).prod f))
    (hB : RevCS (mixedForm f (vs ++ List.replicate (e - 2) w))) (y : Fin d → ℝ) :
    eval w ((vs.map dirDeriv).prod f) *
        eval w (dirDeriv y (dirDeriv y ((vs.map dirDeriv).prod f))) ≤
      eval w (dirDeriv y ((vs.map dirDeriv).prod f)) ^ 2 := by
  have hww := mixedForm_append_replicate_self_self hg he w
  have hwy := mixedForm_append_replicate_self_left hg he w y
  have hyy := mixedForm_append_replicate_diag hg w y
  have hBw : 0 < mixedForm f (vs ++ List.replicate (e - 2) w) w w := by
    rw [hww]
    exact mul_pos (by exact_mod_cast Nat.factorial_pos e) hpos
  have key := hB w y hBw
  rw [hww, hwy, hyy] at key
  set G := eval w ((vs.map dirDeriv).prod f)
  set G1 := eval w (dirDeriv y ((vs.map dirDeriv).prod f))
  set G2 := eval w (dirDeriv y (dirDeriv y ((vs.map dirDeriv).prod f)))
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  have hfact : (k + 2).factorial = (k + 2) * ((k + 1) * k.factorial) := rfl
  rw [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega, hfact,
    Nat.factorial_succ] at key
  push_cast at key
  have hF : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hc : 0 < ((k : ℝ) + 1) * (k.factorial : ℝ) ^ 2 := by positivity
  have h2 : ((k : ℝ) + 2) * (G * G2) ≤ ((k : ℝ) + 1) * G1 ^ 2 := by
    refine le_of_mul_le_mul_left ?_ hc
    nlinarith [key]
  nlinarith [sq_nonneg G1]

/-! ### The criterion -/

/-- **Mixed-Lorentzian implies completely log-concave** ([BH20, Proposition 2.33], computation). Let `f` be homogeneous of
degree `m` with nonnegative coefficients. If the mixed form `B_f[us]` satisfies `RevCS` for
every list `us` of `m - 2` positive directions, then `f` is completely log-concave. -/
theorem completelyLogConcave_of_revCS {d m : ℕ} (f : MvPolynomial (Fin d) ℝ)
    (hcoeff : ∀ a, 0 ≤ f.coeff a) (hf : f.IsHomogeneous m)
    (h : ∀ us : List (Fin d → ℝ), us.length + 2 = m → (∀ u ∈ us, ∀ i, 0 < u i) →
      RevCS (mixedForm f us)) :
    CompletelyLogConcave f := by
  refine ⟨hcoeff, fun vs hvs => ?_⟩
  by_cases hg0 : (vs.map dirDeriv).prod f = 0
  · exact Or.inl hg0
  have hgpos : ∀ z ∈ posOrthant d, 0 < eval z ((vs.map dirDeriv).prod f) :=
    fun z hz => eval_pos_of_coeff_nonneg (coeff_prod_dirDeriv_nonneg hcoeff hvs) hg0 hz
  refine Or.inr (concaveOn_log_eval_of_sq_le hgpos fun w hw y => ?_)
  have hg := isHomogeneous_prod_dirDeriv hf vs
  rcases le_or_gt (m - vs.length) 1 with he | he
  · rw [dirDeriv_dirDeriv_eq_zero hg he, map_zero, mul_zero]
    exact sq_nonneg _
  · have hB := revCS_mixedForm_append_of_nonneg h hvs (us := List.replicate (m - vs.length - 2) w)
      (fun u hu => by rw [List.eq_of_mem_replicate hu]; exact hw)
      (by rw [List.length_replicate]; omega)
    exact eval_mul_eval_dirDeriv_dirDeriv_le hg he (hgpos w hw) hB y

end Parking

end
