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

public import Parking.External
public import Parking.MConvexForms
import Parking.CLCCriterion
import Parking.PerronStep

/-!
# The generating function of an M-convex set is completely log-concave

This module proves the citation interface
`BH20.SupportGenFunCLC` (`bh20_supportGenFunCLC`).

The core is `revCS_mixedForm_supportGenFun`: for `J` M-convex with all exponents of degree
`m` and positive directions `u₁, …, u_{m-2}`, the mixed form `B_{f_J}[u₁, …, u_{m-2}]` satisfies
the reverse Cauchy–Schwarz inequality. The proof is an induction on `m`:

- for `m = 2`, it is the quadratic case `revCS_mixedForm_supportGenFun_two` from `Parking.MConvexForms`,
  which follows the proof of [BH20, Lemma 3.11] (Brändén–Huh, *Lorentzian polynomials*,
  arXiv:1902.03719);
- for `m ≥ 3`, it is the induction step `revCS_mixedForm_append_of_pderiv`, which is
  Brändén–Leake, *Lorentzian polynomials on cones*, arXiv:2304.13203v2, Theorem 2.10, with
  the Perron step `rcs_of_perron` (their Lemma 2.8), for the cone `ℝ^d_{>0}`. With
  `B = B_f[us, w]`, `B_k = B_{∂_k f}[us]` and `A k l = B(e_k, e_l)`, the Euler decomposition
  `B = ∑_k w_k B_k` and `RevCS(B_k)` at `w` give (★); for `(A w)_k = 0`, `∂_k f = 0` and
  `B_k = 0`. Connectivity comes from `IsMConvex.reflTransGen_pderiv`, and the derivatives
  `∂_k f_J = f_{J / e_k}` are again generating functions of M-convex sets, of degree `m - 1`.
  The case `f = 0` (`J` empty) gives the zero form.

Complete log-concavity then follows from the criterion `completelyLogConcave_of_revCS`
in `Parking.CLCCriterion`. In degrees `m ≤ 1` there is no list of `m - 2` directions, and the hypothesis of
the criterion is vacuous.
-/

public section

open MvPolynomial Matrix

namespace Parking

/-- The mixed form of the zero polynomial satisfies `RevCS`. -/
theorem revCS_mixedForm_zero {d : ℕ} (us : List (Fin d → ℝ)) :
    RevCS (mixedForm (0 : MvPolynomial (Fin d) ℝ) us) := by
  have h : mixedForm (0 : MvPolynomial (Fin d) ℝ) us = fun _ _ => 0 := by
    funext x y
    exact mixedForm_zero us x y
  rw [h]
  exact revCS_zero

/-- **Induction step** (Brändén–Leake, *Lorentzian polynomials on cones*,
arXiv:2304.13203v2, Theorem 2.10, with the Perron step of their Lemma 2.8, for the cone
`ℝ^d_{>0}`). Let `f` be homogeneous of degree `us.length + 3` with nonnegative coefficients,
such that the graph `∂_a ∂_b f ≠ 0` connects any two coordinates `i, j` with `∂_i f ≠ 0` and
`∂_j f ≠ 0`. If every mixed form `B_{∂_k f}[us]` satisfies `RevCS`, then so does
`B_f[us, w]` for every `w > 0`. -/
theorem revCS_mixedForm_append_of_pderiv {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hf : f.IsHomogeneous m) (hcoeff : ∀ n, 0 ≤ f.coeff n) {us : List (Fin d → ℝ)}
    {w : Fin d → ℝ} (hlen : us.length + 3 = m) (hus : ∀ u ∈ us, ∀ i, 0 < u i)
    (hw : ∀ i, 0 < w i)
    (hconn : ∀ i j, pderiv i f ≠ 0 → pderiv j f ≠ 0 →
      Relation.ReflTransGen (fun a b => pderiv a (pderiv b f) ≠ 0) i j)
    (hder : ∀ k, RevCS (mixedForm (pderiv k f) us)) :
    RevCS (mixedForm f (us ++ [w])) := by
  have hlen' : (us ++ [w]).length + 2 = m := by
    rw [List.length_append, List.length_singleton]
    omega
  have hpos : ∀ u ∈ us ++ [w], ∀ i, 0 < u i := by
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact hus u hu
    · rw [List.mem_singleton.1 hu]
      exact hw
  by_cases hf0 : f = 0
  · rw [hf0]
    exact revCS_mixedForm_zero _
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A = of fun k l => mixedForm f (us ++ [w]) (Pi.single k 1) (Pi.single l 1) := ⟨_, rfl⟩
  -- `(A y)_k = B(e_k, y) = B_k(y, w)`
  have hAv : ∀ y k, (A *ᵥ y) k = mixedForm (pderiv k f) us y w := by
    intro y k
    rw [hA, mulVec_mixedForm, mixedForm_comm, mixedForm_pderiv]
  -- `(A w)_k > 0` if and only if `∂_k f ≠ 0`
  have hAw : ∀ k, 0 < (A *ᵥ w) k ↔ pderiv k f ≠ 0 := by
    intro k
    rw [hA, mulVec_mixedForm, mixedForm_comm]
    exact mixedForm_single_pos_iff hf hcoeff hpos hlen' hw k
  have hdot : ∀ x y, x ⬝ᵥ (A *ᵥ y) = mixedForm f (us ++ [w]) x y := fun x y => by
    rw [hA]
    exact (mixedForm_eq_dotProduct_mulVec f _ x y).symm
  have hsingle : ∀ k i, 0 ≤ (Pi.single k (1 : ℝ) : Fin d → ℝ) i := fun k =>
    Pi.single_nonneg.2 zero_le_one
  have key := rcs_of_perron A w (by rw [hA]; exact isSymm_mixedForm f _)
    (fun i j => by
      rw [hA, of_apply]
      exact mixedForm_nonneg hcoeff (fun u hu i => (hpos u hu i).le) (hsingle i) (hsingle j))
    hw
    (fun i j hi hj => by
      refine Relation.ReflTransGen.mono (fun a b hab => ?_) i j
        (hconn i j ((hAw i).1 hi) ((hAw j).1 hj))
      rw [hA, of_apply]
      exact (mixedForm_single_single_pos_iff hf hcoeff hpos hlen' a b).2 hab)
    (fun z => by
      -- (★), from the Euler decomposition `B = ∑_k w_k B_k` and `RevCS(B_k)` at `w`
      rw [hdot, mixedForm_append]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [hAv z k, hAv w k]
      split_ifs with hk
      · have h1 := hder k w z hk
        rw [mixedForm_comm (pderiv k f) us w z] at h1
        rw [le_div_iff₀ hk]
        calc w k * mixedForm (pderiv k f) us z z * mixedForm (pderiv k f) us w w
            = w k * (mixedForm (pderiv k f) us w w * mixedForm (pderiv k f) us z z) := by
              ring
          _ ≤ w k * mixedForm (pderiv k f) us z w ^ 2 :=
              mul_le_mul_of_nonneg_left h1 (hw k).le
      · have hk0 : pderiv k f = 0 := by
          by_contra hne
          exact hk (hAv w k ▸ (hAw k).2 hne)
        rw [hk0, mixedForm_zero, mul_zero])
  refine revCS_of_at _ w (mixedForm_comm f _) (mixedForm_add_left f _)
    (mixedForm_smul_left f _) (mixedForm_pos hf hcoeff hf0 hpos hlen' hw hw) fun z => ?_
  have hz := key z
  rw [hdot, hdot, hdot] at hz
  exact hz

/-- **Mixed-Lorentzian property of `f_J`** (Brändén–Leake, *Lorentzian polynomials on cones*,
arXiv:2304.13203v2, Theorem 2.10 and Lemma 2.8, for the cone `ℝ^d_{>0}`; the base case
`m = 2` is the proof of [BH20, Lemma 3.11]). For `J` M-convex with all exponents of degree
`m` and positive directions `u₁, …, u_{m-2}`, the mixed form `B_{f_J}[u₁, …, u_{m-2}]`
satisfies the reverse Cauchy–Schwarz inequality. Plain induction on `m`, generalizing `J`
and the directions. -/
theorem revCS_mixedForm_supportGenFun {d m : ℕ} (J : Finset (Fin d →₀ ℕ))
    (hdeg : ∀ α ∈ J, α.degree = m) (hJ : IsMConvex (J : Set (Fin d →₀ ℕ)))
    (us : List (Fin d → ℝ)) (hus : us.length + 2 = m) (hpos : ∀ u ∈ us, ∀ i, 0 < u i) :
    RevCS (mixedForm (supportGenFun J) us) := by
  induction m generalizing J us with
  | zero => omega
  | succ m ih =>
    rcases List.eq_nil_or_concat' us with rfl | ⟨us', w, rfl⟩
    · -- the quadratic case
      rw [List.length_nil] at hus
      have hm : m + 1 = 2 := by omega
      rw [hm] at hdeg
      exact revCS_mixedForm_supportGenFun_two hdeg hJ
    · -- the induction step
      rw [List.length_append, List.length_singleton] at hus
      have hlen : us'.length + 2 = m := by omega
      have hpos' : ∀ u ∈ us', ∀ i, 0 < u i := fun u hu =>
        hpos u (List.mem_append_left _ hu)
      have hw : ∀ i, 0 < w i := hpos w (List.mem_append_right _ (List.mem_singleton_self w))
      refine revCS_mixedForm_append_of_pderiv (isHomogeneous_supportGenFun hdeg)
        (coeff_supportGenFun_nonneg J) (by omega) hpos' hw
        (hJ.reflTransGen_pderiv (by omega) hdeg) fun k => ?_
      rw [pderiv_supportGenFun]
      refine ih (contractSet J k) (fun γ hγ => ?_) (hJ.contractSet k) us' hlen hpos'
      have h := degree_of_mem_contractSet hdeg hγ
      rwa [Nat.add_sub_cancel] at h

/-- **`BH20.SupportGenFunCLC` is proved.** The generating function of a nonempty M-convex set of exponents, all of
total degree `m`, is completely log-concave: the criterion `completelyLogConcave_of_revCS`
(`Parking.CLCCriterion`) applied to `revCS_mixedForm_supportGenFun`. -/
theorem bh20_supportGenFunCLC : BH20.SupportGenFunCLC := by
  intro d m J _ hdeg hJ
  exact completelyLogConcave_of_revCS _ (coeff_supportGenFun_nonneg J)
    (isHomogeneous_supportGenFun hdeg) fun us hus hpos =>
      revCS_mixedForm_supportGenFun J hdeg hJ us hus hpos

end Parking

end
