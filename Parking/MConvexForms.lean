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
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# M-convex specifics of the generating function `f_J`

Here `J` is a finite set of
exponents, `f_J = ∑_{α ∈ J} x^α / α!` is `supportGenFun J`, and `IsMConvex` is the exchange
property of [BH20, p. 9].

Main results:

- **contractions**: `contractSet J k = J / e_k = {β - e_k | β ∈ J, β_k ≥ 1}`, with
  `pderiv_supportGenFun` (`∂_k f_J = f_{J / e_k}`) and `IsMConvex.contractSet` (`J / e_k`
  is M-convex); `degree_of_mem_contractSet` (the degree drops by one), the emptiness
  criteria `contractSet_nonempty_iff`, `contractSet_eq_empty_iff`, and the non-vanishing
  criteria `supportGenFun_ne_zero_iff`, `pderiv_supportGenFun_ne_zero_iff`,
  `pderiv_pderiv_supportGenFun_ne_zero_iff` (and its cases `_of_ne`, `_self`);
- **connectivity**: `IsMConvex.reflTransGen`. For `J` M-convex of degree `m ≥ 2`, any two
  active coordinates are joined by a chain of pairs `a ≠ b` that appear together in some
  `γ ∈ J`. Exchange steps lead from one exponent to another, and consecutive supports
  meet. The form used in `Parking.SupportGenFunCLC` is `IsMConvex.reflTransGen_pderiv`, with the relation
  `∂_a ∂_b f_J ≠ 0`;
- **the quadratic case**: `revCS_mixedForm_supportGenFun_two`. This follows the proof of
  [BH20, Lemma 3.11] (Brändén–Huh, *Lorentzian polynomials*, arXiv:1902.03719), with the
  plain exchange property and one exchange for each claim.
  With `V` the active coordinates and `S = {i | 2 e_i ∈ J}`, the Hessian of `f_J` is
  `[e_k + e_l ∈ J] = [k ∈ V] [l ∈ V] - [k ∼ l]`, where `k ∼ l` means `k, l ∈ V \ S` and
  `e_k + e_l ∉ J`. This relation is symmetric and transitive, so its indicator matrix is
  positive semidefinite (`sum_mul_ite_mul_nonneg`, without quotient types), and Aczél's
  inequality `revCS_rankOne_sub` concludes.

The auxiliary lemmas `isHomogeneous_supportGenFun` and `coeff_supportGenFun_nonneg` give the
hypotheses of the positivity lemmas of `Parking.MixedForm` for `f_J`.
-/

public section

open MvPolynomial

namespace Parking

variable {d : ℕ}

/-! ### The generating function `f_J` -/

/-- The coefficient of `x^n` in `f_J` is `1 / n!` if `n ∈ J`, and `0` otherwise. -/
theorem coeff_supportGenFun_ite (J : Finset (Fin d →₀ ℕ)) (n : Fin d →₀ ℕ) :
    (supportGenFun J).coeff n = if n ∈ J then (∏ i, ((n i).factorial : ℝ))⁻¹ else 0 := by
  rw [supportGenFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']

/-- The coefficients of `f_J` are nonnegative. -/
theorem coeff_supportGenFun_nonneg (J : Finset (Fin d →₀ ℕ)) (n : Fin d →₀ ℕ) :
    0 ≤ (supportGenFun J).coeff n := by
  rw [coeff_supportGenFun_ite]
  split_ifs
  · positivity
  · exact le_rfl

/-- `f_J` is homogeneous of degree `m` when every exponent of `J` has degree `m`. -/
theorem isHomogeneous_supportGenFun {m : ℕ} {J : Finset (Fin d →₀ ℕ)}
    (hdeg : ∀ α ∈ J, α.degree = m) : (supportGenFun J).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun α hα => isHomogeneous_monomial _ (hdeg α hα)

/-- `f_J` vanishes exactly when `J` is empty. -/
theorem supportGenFun_eq_zero_iff {J : Finset (Fin d →₀ ℕ)} : supportGenFun J = 0 ↔ J = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hc : (supportGenFun J).coeff α = 0 := by
      rw [h]
      simp
    rw [coeff_supportGenFun_ite] at hc
    simp only [hα, ↓reduceIte] at hc
    exact (by positivity : (∏ i, ((α i).factorial : ℝ))⁻¹ ≠ 0) hc
  · rintro rfl
    simp [supportGenFun]

/-- `f_J` is nonzero exactly when `J` is nonempty. -/
theorem supportGenFun_ne_zero_iff {J : Finset (Fin d →₀ ℕ)} :
    supportGenFun J ≠ 0 ↔ J.Nonempty := by
  rw [Ne, supportGenFun_eq_zero_iff, Finset.nonempty_iff_ne_empty]

/-- The value of `f_J` at `0` is `1` if `0 ∈ J`, and `0` otherwise. -/
theorem eval_zero_supportGenFun (J : Finset (Fin d →₀ ℕ)) :
    eval 0 (supportGenFun J) = if (0 : Fin d →₀ ℕ) ∈ J then 1 else 0 := by
  rw [eval_zero_eq_coeff_zero, coeff_supportGenFun_ite]
  simp

/-! ### Contractions -/

/-- The contraction `J / e_k = {β - e_k | β ∈ J, β_k ≥ 1}`, so that `∂_k f_J = f_{J / e_k}`
(`pderiv_supportGenFun`). -/
@[expose] noncomputable def contractSet {d : ℕ} (J : Finset (Fin d →₀ ℕ)) (k : Fin d) :
    Finset (Fin d →₀ ℕ) :=
  (J.filter fun β => 1 ≤ β k).image fun β => β - Finsupp.single k 1

/-- `γ ∈ J / e_k` if and only if `γ + e_k ∈ J`. -/
theorem mem_contractSet {J : Finset (Fin d →₀ ℕ)} {k : Fin d} {γ : Fin d →₀ ℕ} :
    γ ∈ contractSet J k ↔ γ + Finsupp.single k 1 ∈ J := by
  constructor
  · intro h
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_filter] at hβ
    rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hβ.2)]
    exact hβ.1
  · intro h
    refine Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨h, ?_⟩, add_tsub_cancel_right _ _⟩
    simp

/-- The contraction of the empty set is empty. -/
theorem contractSet_empty (k : Fin d) : contractSet (∅ : Finset (Fin d →₀ ℕ)) k = ∅ := by
  simp [contractSet]

/-- `J / e_k` is nonempty exactly when some exponent of `J` uses the coordinate `k`. -/
theorem contractSet_nonempty_iff {J : Finset (Fin d →₀ ℕ)} {k : Fin d} :
    (contractSet J k).Nonempty ↔ ∃ α ∈ J, 1 ≤ α k := by
  rw [contractSet, Finset.image_nonempty, Finset.filter_nonempty_iff]

/-- `J / e_k` is empty exactly when no exponent of `J` uses the coordinate `k`. -/
theorem contractSet_eq_empty_iff {J : Finset (Fin d →₀ ℕ)} {k : Fin d} :
    contractSet J k = ∅ ↔ ∀ α ∈ J, α k = 0 := by
  rw [← Finset.not_nonempty_iff_eq_empty, contractSet_nonempty_iff]
  push Not
  exact forall₂_congr fun α _ => Nat.lt_one_iff

/-- If every exponent of `J` has degree `m`, every exponent of `J / e_k` has degree
`m - 1`. -/
theorem degree_of_mem_contractSet {m : ℕ} {J : Finset (Fin d →₀ ℕ)}
    (hdeg : ∀ α ∈ J, α.degree = m) {k : Fin d} {γ : Fin d →₀ ℕ} (hγ : γ ∈ contractSet J k) :
    γ.degree = m - 1 := by
  have h := hdeg _ (mem_contractSet.1 hγ)
  rw [map_add, Finsupp.degree_single] at h
  omega

/-- `∏_i (n + e_k)_i! = (n_k + 1) ∏_i n_i!`. -/
theorem prod_factorial_add_single (n : Fin d →₀ ℕ) (k : Fin d) :
    ∏ i, (((n + Finsupp.single k 1 : Fin d →₀ ℕ) i).factorial : ℝ) =
      ((n k : ℝ) + 1) * ∏ i, ((n i).factorial : ℝ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun i => ((n i).factorial : ℝ)) (Finset.mem_univ k)]
  have hrest :
      ∏ i ∈ Finset.univ.erase k, (((n + Finsupp.single k 1 : Fin d →₀ ℕ) i).factorial : ℝ) =
        ∏ i ∈ Finset.univ.erase k, ((n i).factorial : ℝ) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hik : k ≠ i := fun h => Finset.ne_of_mem_erase hi h.symm
    simp [hik]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

/-- **Contraction.** `∂_k f_J = f_{J / e_k}`. -/
theorem pderiv_supportGenFun {d : ℕ} (J : Finset (Fin d →₀ ℕ)) (k : Fin d) :
    pderiv k (supportGenFun J) = supportGenFun (contractSet J k) := by
  ext n
  rw [coeff_pderiv, coeff_supportGenFun_ite, coeff_supportGenFun_ite]
  by_cases hn : n + Finsupp.single k 1 ∈ J
  · have hn' : n ∈ contractSet J k := mem_contractSet.2 hn
    simp only [hn, hn', ↓reduceIte]
    rw [prod_factorial_add_single]
    have hP : (∏ i, ((n i).factorial : ℝ)) ≠ 0 := by positivity
    have hk : (n k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · have hn' : n ∉ contractSet J k := fun h => hn (mem_contractSet.1 h)
    simp only [hn, hn', ↓reduceIte, zero_mul]

/-- **Contraction preserves M-convexity.** If `J` is M-convex, so is `J / e_k`. -/
theorem IsMConvex.contractSet {d : ℕ} {J : Finset (Fin d →₀ ℕ)}
    (hJ : IsMConvex (J : Set (Fin d →₀ ℕ))) (k : Fin d) :
    IsMConvex (contractSet J k : Set (Fin d →₀ ℕ)) := by
  intro α hα β hβ i hi
  rw [Finset.mem_coe, mem_contractSet] at hα hβ
  have hi' : (β + Finsupp.single k 1 : Fin d →₀ ℕ) i < (α + Finsupp.single k 1 : Fin d →₀ ℕ) i := by
    simp only [Finsupp.add_apply]
    omega
  obtain ⟨j, hj, hmem⟩ := hJ _ (Finset.mem_coe.2 hα) _ (Finset.mem_coe.2 hβ) i hi'
  refine ⟨j, ?_, ?_⟩
  · simp only [Finsupp.add_apply] at hj
    omega
  · rw [Finset.mem_coe, mem_contractSet]
    have heq : α - Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 =
        α + Finsupp.single k 1 - Finsupp.single i 1 + Finsupp.single j 1 := by
      ext l
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      have hil : 1 ≤ α i := by omega
      split_ifs <;> subst_vars <;> omega
    rw [heq]
    exact Finset.mem_coe.1 hmem

/-! ### Non-vanishing of the derivatives of `f_J` -/

/-- `∂_k f_J ≠ 0` if and only if some exponent of `J` uses the coordinate `k`. -/
theorem pderiv_supportGenFun_ne_zero_iff {J : Finset (Fin d →₀ ℕ)} {k : Fin d} :
    pderiv k (supportGenFun J) ≠ 0 ↔ ∃ α ∈ J, 1 ≤ α k := by
  rw [pderiv_supportGenFun, supportGenFun_ne_zero_iff, contractSet_nonempty_iff]

/-- `∂_k ∂_l f_J ≠ 0` if and only if some `γ ∈ J` has `γ_k ≥ 1` and `γ_l ≥ 1`, with
`γ_k ≥ 2` when `k = l`. -/
theorem pderiv_pderiv_supportGenFun_ne_zero_iff {J : Finset (Fin d →₀ ℕ)} {k l : Fin d} :
    pderiv k (pderiv l (supportGenFun J)) ≠ 0 ↔
      ∃ γ ∈ J, 1 ≤ γ k ∧ 1 ≤ γ l ∧ (k = l → 2 ≤ γ k) := by
  rw [pderiv_supportGenFun, pderiv_supportGenFun_ne_zero_iff]
  constructor
  · rintro ⟨β, hβ, hβk⟩
    refine ⟨_, mem_contractSet.1 hβ, ?_, ?_, ?_⟩
    · simp only [Finsupp.add_apply]
      omega
    · simp
    · rintro rfl
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
  · rintro ⟨γ, hγ, hγk, hγl, hkl⟩
    have hle : Finsupp.single l 1 ≤ γ := Finsupp.single_le_iff.2 hγl
    refine ⟨γ - Finsupp.single l 1, mem_contractSet.2 ?_, ?_⟩
    · rwa [tsub_add_cancel_of_le hle]
    · rw [Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h
      · have := hkl h.symm
        omega
      · omega

/-- For `k ≠ l`, `∂_k ∂_l f_J ≠ 0` if and only if some `γ ∈ J` has `γ_k ≥ 1` and
`γ_l ≥ 1`. -/
theorem pderiv_pderiv_supportGenFun_ne_zero_iff_of_ne {J : Finset (Fin d →₀ ℕ)} {k l : Fin d}
    (hkl : k ≠ l) :
    pderiv k (pderiv l (supportGenFun J)) ≠ 0 ↔ ∃ γ ∈ J, 1 ≤ γ k ∧ 1 ≤ γ l := by
  rw [pderiv_pderiv_supportGenFun_ne_zero_iff]
  refine exists_congr fun γ => and_congr_right fun _ => ?_
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun h' => absurd h' hkl⟩⟩

/-- `∂_k² f_J ≠ 0` if and only if some `γ ∈ J` has `γ_k ≥ 2`. -/
theorem pderiv_pderiv_supportGenFun_ne_zero_iff_self {J : Finset (Fin d →₀ ℕ)} {k : Fin d} :
    pderiv k (pderiv k (supportGenFun J)) ≠ 0 ↔ ∃ γ ∈ J, 2 ≤ γ k := by
  rw [pderiv_pderiv_supportGenFun_ne_zero_iff]
  refine exists_congr fun γ => and_congr_right fun _ => ?_
  exact ⟨fun h => h.2.2 rfl, fun h => ⟨by omega, by omega, fun _ => h⟩⟩

/-! ### Connectivity -/

/-- **Connectivity.** Let `J` be M-convex, with all exponents of degree `m ≥ 2`. Any two
active coordinates `i, j` are joined by a chain of pairs `a ≠ b` that both appear in some
`γ ∈ J`. Proof: exchange steps from `α ∋ i` toward `β ∋ j` each decrease
`∑_l (β_l - α_l)`; consecutive exponents share a coordinate, since an exponent whose support
is one point `a` has `γ_a = m ≥ 2`. -/
theorem IsMConvex.reflTransGen {d m : ℕ} {J : Finset (Fin d →₀ ℕ)} (hm : 2 ≤ m)
    (hdeg : ∀ α ∈ J, α.degree = m) (hJ : IsMConvex (J : Set (Fin d →₀ ℕ))) (i j : Fin d)
    (hi : ∃ α ∈ J, 1 ≤ α i) (hj : ∃ β ∈ J, 1 ≤ β j) :
    Relation.ReflTransGen (fun a b => a ≠ b ∧ ∃ γ ∈ J, 1 ≤ γ a ∧ 1 ≤ γ b) i j := by
  -- two coordinates in the support of one exponent are related
  have hsupp : ∀ γ ∈ J, ∀ a b, 1 ≤ γ a → 1 ≤ γ b →
      Relation.ReflTransGen (fun a b => a ≠ b ∧ ∃ γ ∈ J, 1 ≤ γ a ∧ 1 ≤ γ b) a b := by
    intro γ hγ a b ha hb
    by_cases hab : a = b
    · rw [hab]
    · exact Relation.ReflTransGen.single ⟨hab, γ, hγ, ha, hb⟩
  obtain ⟨α, hα, hαi⟩ := hi
  obtain ⟨β, hβ, hβj⟩ := hj
  suffices H : ∀ n, ∀ α ∈ J, ∑ l, (β l - α l) = n → ∀ a, 1 ≤ α a →
      Relation.ReflTransGen (fun a b => a ≠ b ∧ ∃ γ ∈ J, 1 ≤ γ a ∧ 1 ≤ γ b) a j from
    H _ α hα rfl i hαi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α hα hn a ha
  by_cases hαβ : α = β
  · rw [hαβ] at ha
    exact hsupp β hβ a j ha hβj
  -- a coordinate where `α` exceeds `β`
  obtain ⟨i', hi'⟩ : ∃ i', β i' < α i' := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l, hl⟩ : ∃ l, α l < β l := by
      by_contra h2
      push Not at h2
      exact hαβ (Finsupp.ext fun l => le_antisymm (hcon l) (h2 l))
    have hlt : ∑ l, α l < ∑ l, β l :=
      Finset.sum_lt_sum (fun l _ => hcon l) ⟨l, Finset.mem_univ l, hl⟩
    rw [← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, hdeg α hα, hdeg β hβ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨j', hj', hγ⟩ := hJ α (Finset.mem_coe.2 hα) β (Finset.mem_coe.2 hβ) i' hi'
  have hγapp : ∀ l, (α - Finsupp.single i' 1 + Finsupp.single j' 1 : Fin d →₀ ℕ) l =
      α l - (if i' = l then 1 else 0) + (if j' = l then 1 else 0) := by
    intro l
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  -- the exchange decreases `∑_l (β_l - α_l)`
  have hlt : ∑ l, (β l - (α - Finsupp.single i' 1 + Finsupp.single j' 1 : Fin d →₀ ℕ) l) < n := by
    rw [← hn]
    refine Finset.sum_lt_sum (fun l _ => ?_) ⟨j', Finset.mem_univ _, ?_⟩
    · rw [hγapp]
      split_ifs <;> subst_vars <;> omega
    · rw [hγapp]
      split_ifs <;> subst_vars <;> omega
  -- `α` and the exchanged exponent share a coordinate `c`
  obtain ⟨c, hcα, hcγ⟩ : ∃ c, 1 ≤ α c ∧
      1 ≤ (α - Finsupp.single i' 1 + Finsupp.single j' 1 : Fin d →₀ ℕ) c := by
    by_cases h2 : 2 ≤ α i'
    · refine ⟨i', by omega, ?_⟩
      rw [hγapp]
      split_ifs <;> subst_vars <;> omega
    · obtain ⟨c, hc, hci⟩ : ∃ c, 1 ≤ α c ∧ c ≠ i' := by
        by_contra hcon
        push Not at hcon
        have hdα : α.degree = α i' := by
          rw [Finsupp.degree_eq_sum, Finset.sum_eq_single i']
          · intro b _ hb
            by_contra h0
            exact hb (hcon b (Nat.one_le_iff_ne_zero.2 h0))
          · simp
        rw [hdeg α hα] at hdα
        omega
      refine ⟨c, hc, ?_⟩
      rw [hγapp]
      split_ifs <;> subst_vars <;> omega
  exact (hsupp α hα a c ha hcα).trans (ih _ hlt _ (Finset.mem_coe.1 hγ) rfl c hcγ)

/-- **Connectivity, derivative form** (the hypothesis `hconn` of `rcs_of_perron`, through
`mixedForm_single_single_pos_iff`): for `J` M-convex of degree `m ≥ 2`, the graph
`∂_a ∂_b f_J ≠ 0` connects any two coordinates `i, j` with `∂_i f_J ≠ 0` and
`∂_j f_J ≠ 0`. -/
theorem IsMConvex.reflTransGen_pderiv {d m : ℕ} {J : Finset (Fin d →₀ ℕ)} (hm : 2 ≤ m)
    (hdeg : ∀ α ∈ J, α.degree = m) (hJ : IsMConvex (J : Set (Fin d →₀ ℕ))) (i j : Fin d)
    (hi : pderiv i (supportGenFun J) ≠ 0) (hj : pderiv j (supportGenFun J) ≠ 0) :
    Relation.ReflTransGen (fun a b => pderiv a (pderiv b (supportGenFun J)) ≠ 0) i j := by
  have h := hJ.reflTransGen hm hdeg i j (pderiv_supportGenFun_ne_zero_iff.1 hi)
    (pderiv_supportGenFun_ne_zero_iff.1 hj)
  clear hi hj
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact ih.tail ((pderiv_pderiv_supportGenFun_ne_zero_iff_of_ne hbc.1).2 hbc.2)

/-! ### The quadratic case -/

/-- The Hessian of `f_J`: `B_{f_J}[](e_k, e_l) = [e_k + e_l ∈ J]`. -/
theorem mixedForm_supportGenFun_single_single (J : Finset (Fin d →₀ ℕ)) (k l : Fin d) :
    mixedForm (supportGenFun J) [] (Pi.single k 1) (Pi.single l 1) =
      if Finsupp.single k 1 + Finsupp.single l 1 ∈ J then 1 else 0 := by
  rw [mixedForm_nil, dirDeriv_single, dirDeriv_single]
  change eval 0 (pderiv k (pderiv l (supportGenFun J))) = _
  rw [pderiv_supportGenFun, pderiv_supportGenFun, eval_zero_supportGenFun]
  simp only [mem_contractSet, zero_add]

/-- An exponent of degree `2` with a unit at `l` is `e_l + e_b` for some `b`. -/
theorem exists_eq_single_add_single {α : Fin d →₀ ℕ} (hα : α.degree = 2) {l : Fin d}
    (hl : 1 ≤ α l) : ∃ b, α = Finsupp.single l 1 + Finsupp.single b 1 := by
  have hdeg : ∀ {γ : Fin d →₀ ℕ} {a : Fin d}, 1 ≤ γ a →
      (γ - Finsupp.single a 1).degree + 1 = γ.degree := by
    intro γ a ha
    conv_rhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.2 ha)]
    rw [map_add, Finsupp.degree_single]
  have h1 : (α - Finsupp.single l 1).degree = 1 := by
    have := hdeg hl
    omega
  obtain ⟨b, hb⟩ : ∃ b, 1 ≤ (α - Finsupp.single l 1 : Fin d →₀ ℕ) b := by
    by_contra hcon
    push Not at hcon
    have h0 : α - Finsupp.single l 1 = 0 := Finsupp.ext fun b => by
      have := hcon b
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have h0 : α - Finsupp.single l 1 - Finsupp.single b 1 = 0 := by
    have := hdeg hb
    rw [h1] at this
    exact (Finsupp.degree_eq_zero_iff _).1 (by omega)
  have hle1 : Finsupp.single l 1 ≤ α := Finsupp.single_le_iff.2 hl
  have hle2 : Finsupp.single b 1 ≤ α - Finsupp.single l 1 := Finsupp.single_le_iff.2 hb
  refine ⟨b, ?_⟩
  rw [← tsub_add_cancel_of_le hle1, ← tsub_add_cancel_of_le hle2, h0, zero_add, add_comm]

/-- **One exchange, in pair form.** If `e_a + e_b ∈ J`, `β ∈ J` and `β_b = 0`, then
`e_a + e_m ∈ J` for some `m` with `β_m > 0`. -/
theorem IsMConvex.exists_single_add_single_mem {J : Finset (Fin d →₀ ℕ)}
    (hJ : IsMConvex (J : Set (Fin d →₀ ℕ))) {a b : Fin d}
    (hab : Finsupp.single a 1 + Finsupp.single b 1 ∈ J) {β : Fin d →₀ ℕ} (hβ : β ∈ J)
    (hβb : β b = 0) : ∃ m, 0 < β m ∧ Finsupp.single a 1 + Finsupp.single m 1 ∈ J := by
  obtain ⟨m, hm, hmem⟩ := hJ _ (Finset.mem_coe.2 hab) β (Finset.mem_coe.2 hβ) b (by
    simp only [hβb, Finsupp.add_apply, Finsupp.single_eq_same]
    omega)
  refine ⟨m, by omega, ?_⟩
  rw [add_tsub_cancel_right] at hmem
  exact Finset.mem_coe.1 hmem

/-- `(e_i + e_k)_m > 0` if and only if `m = i` or `m = k`. -/
theorem single_add_single_pos_iff {i k m : Fin d} :
    0 < (Finsupp.single i 1 + Finsupp.single k 1 : Fin d →₀ ℕ) m ↔ m = i ∨ m = k := by
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

/-- **First claim of the quadratic case** (one exchange). For `J` M-convex of degree `2`,
if `2 e_k ∈ J` and `l` is active, then `e_k + e_l ∈ J`. -/
theorem IsMConvex.single_add_single_mem_of_double {J : Finset (Fin d →₀ ℕ)}
    (hJ : IsMConvex (J : Set (Fin d →₀ ℕ))) (hdeg : ∀ α ∈ J, α.degree = 2) {k l : Fin d}
    (hk : Finsupp.single k 1 + Finsupp.single k 1 ∈ J) (hl : ∃ α ∈ J, 1 ≤ α l) :
    Finsupp.single k 1 + Finsupp.single l 1 ∈ J := by
  obtain ⟨α, hα, hαl⟩ := hl
  obtain ⟨b, rfl⟩ := exists_eq_single_add_single (hdeg _ hα) hαl
  by_cases hbk : b = k
  · rw [← hbk, add_comm]
    exact hα
  · obtain ⟨m, hm, hmem⟩ := hJ.exists_single_add_single_mem hα hk (by
      simp [Ne.symm hbk])
    rw [single_add_single_pos_iff, or_self] at hm
    rw [hm, add_comm] at hmem
    exact hmem

/-- **Second claim of the quadratic case** (one exchange). For `J` M-convex of degree `2`,
if `e_i + e_k ∈ J` and `j` is active, then `e_j + e_i ∈ J` or `e_j + e_k ∈ J`. -/
theorem IsMConvex.single_add_single_mem_or {J : Finset (Fin d →₀ ℕ)}
    (hJ : IsMConvex (J : Set (Fin d →₀ ℕ))) (hdeg : ∀ α ∈ J, α.degree = 2) {i j k : Fin d}
    (hik : Finsupp.single i 1 + Finsupp.single k 1 ∈ J) (hj : ∃ α ∈ J, 1 ≤ α j) :
    Finsupp.single j 1 + Finsupp.single i 1 ∈ J ∨
      Finsupp.single j 1 + Finsupp.single k 1 ∈ J := by
  obtain ⟨α, hα, hαj⟩ := hj
  obtain ⟨l, rfl⟩ := exists_eq_single_add_single (hdeg _ hα) hαj
  by_cases hli : l = i
  · rw [hli] at hα
    exact Or.inl hα
  by_cases hlk : l = k
  · rw [hlk] at hα
    exact Or.inr hα
  obtain ⟨m, hm, hmem⟩ := hJ.exists_single_add_single_mem hα hik (by
    simp [Ne.symm hli, Ne.symm hlk])
  rcases single_add_single_pos_iff.1 hm with rfl | rfl
  · exact Or.inl hmem
  · exact Or.inr hmem

/-- **The indicator matrix of a partial equivalence relation is positive semidefinite.**
With `C(k) = {l | k ∼ l}`, `[i ∼ j] = ∑_k [k ∼ i] [k ∼ j] / |C(k)|`, so that
`∑_{i,j} x_i [i ∼ j] x_j = ∑_k (∑_{i ∼ k} x_i)² / |C(k)| ≥ 0`. No quotient type is
needed. -/
theorem sum_mul_ite_mul_nonneg (r : Fin d → Fin d → Prop) [DecidableRel r]
    (hsymm : ∀ i j, r i j → r j i) (htrans : ∀ i j k, r i j → r j k → r i k)
    (x : Fin d → ℝ) : 0 ≤ ∑ i, ∑ j, x i * (if r i j then 1 else 0) * x j := by
  obtain ⟨c, hc⟩ : ∃ c : Fin d → ℝ, ∀ k, c k = ((Finset.univ.filter (r k)).card : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have key : ∀ i j, (if r i j then (1 : ℝ) else 0) =
      ∑ k, (if r k i then (1 : ℝ) else 0) * (if r k j then 1 else 0) / c k := by
    intro i j
    by_cases hij : r i j
    · have hii : r i i := htrans _ _ _ hij (hsymm _ _ hij)
      have hterm : ∀ k, (if r k i then (1 : ℝ) else 0) * (if r k j then 1 else 0) / c k =
          (if r k i then 1 else 0) / c i := by
        intro k
        by_cases hki : r k i
        · have hck : c k = c i := by
            rw [hc, hc]
            congr 2
            ext m
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun hkm => htrans _ _ _ (hsymm _ _ hki) hkm, fun him => htrans _ _ _ hki him⟩
          simp [hki, htrans _ _ _ hki hij, hck]
        · simp [hki]
      rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_div, Finset.sum_boole]
      have hcard : (Finset.univ.filter fun k => r k i) = Finset.univ.filter (r i) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hsymm _ _, hsymm _ _⟩
      have hpos : (0 : ℝ) < c i := by
        rw [hc]
        exact_mod_cast Finset.card_pos.2 ⟨i, by simp [hii]⟩
      rw [hcard, ← hc]
      simp only [hij, ↓reduceIte]
      field_simp
    · simp only [hij, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hki : r k i
      · have hkj : ¬r k j := fun hkj => hij (htrans _ _ _ (hsymm _ _ hki) hkj)
        simp [hkj]
      · simp [hki]
  have hexp : ∑ i, ∑ j, x i * (if r i j then 1 else 0) * x j =
      ∑ k, (∑ i, (if r k i then (1 : ℝ) else 0) * x i) ^ 2 / c k := by
    calc ∑ i, ∑ j, x i * (if r i j then 1 else 0) * x j
        = ∑ i, ∑ j, ∑ k, (if r k i then (1 : ℝ) else 0) * x i *
            ((if r k j then 1 else 0) * x j) / c k := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [key i j, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = ∑ i, ∑ k, ∑ j, (if r k i then (1 : ℝ) else 0) * x i *
            ((if r k j then 1 else 0) * x j) / c k :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (if r k i then (1 : ℝ) else 0) * x i *
            ((if r k j then 1 else 0) * x j) / c k := Finset.sum_comm
      _ = ∑ k, (∑ i, (if r k i then (1 : ℝ) else 0) * x i) ^ 2 / c k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sq, Finset.sum_mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_div]
  rw [hexp]
  refine Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) ?_
  rw [hc]
  exact Nat.cast_nonneg _

/-- **The quadratic case** ([BH20, Lemma 3.11], its proof). For `J` M-convex with all
exponents of degree `2`, the Hessian form of `f_J` satisfies the reverse Cauchy–Schwarz
inequality. It is `ℓ(x) ℓ(y) - Σ(x, y)`, with `ℓ` the sum of the active coordinates and
`Σ` the indicator form of the relation `k ∼ l` (`k, l` active, `2 e_k, 2 e_l, e_k + e_l ∉ J`),
which is symmetric and transitive by one exchange; Aczél's inequality concludes. -/
theorem revCS_mixedForm_supportGenFun_two {d : ℕ} {J : Finset (Fin d →₀ ℕ)}
    (hdeg : ∀ α ∈ J, α.degree = 2) (hJ : IsMConvex (J : Set (Fin d →₀ ℕ))) :
    RevCS (mixedForm (supportGenFun J) []) := by
  classical
  obtain ⟨act, hact⟩ : ∃ act : Fin d → Prop, ∀ k, act k ↔ ∃ α ∈ J, 1 ≤ α k :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Fin d → Fin d → Prop,
      ∀ k l, E k l ↔ Finsupp.single k 1 + Finsupp.single l 1 ∈ J := ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨rel, hrel⟩ : ∃ rel : Fin d → Fin d → Prop,
      ∀ k l, rel k l ↔ act k ∧ act l ∧ ¬E k k ∧ ¬E l l ∧ ¬E k l := ⟨_, fun _ _ => Iff.rfl⟩
  have hEcomm : ∀ k l, E k l → E l k := by
    intro k l h
    rw [hE] at h ⊢
    rwa [add_comm]
  have hEact : ∀ k l, E k l → act k := by
    intro k l h
    rw [hE] at h
    rw [hact]
    exact ⟨_, h, by simp [Finsupp.single_apply]⟩
  have hsymm : ∀ i j, rel i j → rel j i := by
    intro i j h
    rw [hrel] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨h2, h1, h4, h3, fun h => h5 (hEcomm _ _ h)⟩
  have htrans : ∀ i j k, rel i j → rel j k → rel i k := by
    intro i j k hij hjk
    rw [hrel] at hij hjk ⊢
    obtain ⟨hi, hj, hii, -, hij⟩ := hij
    obtain ⟨-, hk, -, hkk, hjk⟩ := hjk
    refine ⟨hi, hk, hii, hkk, fun hik => ?_⟩
    rcases hJ.single_add_single_mem_or hdeg ((hE _ _).1 hik) ((hact j).1 hj) with h | h
    · exact hij (hEcomm _ _ ((hE _ _).2 h))
    · exact hjk ((hE _ _).2 h)
  -- the Hessian entries
  have hentry : ∀ k l, mixedForm (supportGenFun J) [] (Pi.single k 1) (Pi.single l 1) =
      (if act k then 1 else 0) * (if act l then 1 else 0) - (if rel k l then 1 else 0) := by
    intro k l
    rw [mixedForm_supportGenFun_single_single]
    by_cases h1 : E k l
    · have hk := hEact k l h1
      have hl := hEact l k (hEcomm k l h1)
      have hr : ¬rel k l := fun h => ((hrel k l).1 h).2.2.2.2 h1
      simp [(hE k l).1 h1, hk, hl, hr]
    · have h1' : Finsupp.single k 1 + Finsupp.single l 1 ∉ J := fun h => h1 ((hE k l).2 h)
      by_cases hk : act k
      · by_cases hl : act l
        · have hr : rel k l := by
            refine (hrel k l).2 ⟨hk, hl, fun hkk => h1 ?_, fun hll => h1 ?_, h1⟩
            · exact (hE _ _).2
                (hJ.single_add_single_mem_of_double hdeg ((hE _ _).1 hkk) ((hact l).1 hl))
            · exact hEcomm _ _ ((hE _ _).2
                (hJ.single_add_single_mem_of_double hdeg ((hE _ _).1 hll) ((hact k).1 hk)))
          simp [h1', hk, hl, hr]
        · have hr : ¬rel k l := fun h => hl ((hrel k l).1 h).2.1
          simp [h1', hl, hr]
      · have hr : ¬rel k l := fun h => hk ((hrel k l).1 h).1
        simp [h1', hk, hr]
  -- the linear form `ℓ` and the positive semidefinite form `Σ`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      ∀ x, ℓ x = ∑ k, (if act k then (1 : ℝ) else 0) * x k :=
    ⟨{ toFun := fun x => ∑ k, (if act k then (1 : ℝ) else 0) * x k
       map_add' := fun x y => by
         simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
       map_smul' := fun c x => by
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
         exact Finset.sum_congr rfl fun k _ => by ring }, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : LinearMap.BilinForm ℝ (Fin d → ℝ),
      ∀ x y, S x y = ∑ i, ∑ j, x i * (if rel i j then 1 else 0) * y j :=
    ⟨Matrix.toBilin' (Matrix.of fun i j => if rel i j then (1 : ℝ) else 0),
      fun x y => by rw [Matrix.toBilin'_apply]; rfl⟩
  have hSsymm : S.IsSymm := by
    refine ⟨fun x y => ?_⟩
    rw [hS, hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : (if rel j i then (1 : ℝ) else 0) = if rel i j then 1 else 0 := by
      by_cases h : rel i j
      · simp [h, hsymm _ _ h]
      · have h' : ¬rel j i := fun h' => h (hsymm _ _ h')
        simp [h, h']
    rw [hij]
    ring
  have hSpos : ∀ x, 0 ≤ S x x := fun x => by
    rw [hS]
    exact sum_mul_ite_mul_nonneg rel hsymm htrans x
  have hform : mixedForm (supportGenFun J) [] = fun x y => ℓ x * ℓ y - S x y := by
    funext x y
    rw [mixedForm_eq_sum, hℓ, hℓ, hS, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hentry]
    ring
  rw [hform]
  exact revCS_rankOne_sub ℓ S hSsymm hSpos

end Parking
