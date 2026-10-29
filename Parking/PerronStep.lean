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

public import Mathlib.Analysis.Matrix.PosDef

/-!
# The Perron step

A linear-algebra criterion for the reverse Cauchy–Schwarz inequality.

Let `A` be a symmetric matrix with nonnegative entries, `w > 0`, `r = A w`, and
`K = {k | 0 < r k}`. Assume that the graph `{A k l > 0}` connects any two points of `K`, and
(★) `zᵀ A z ≤ ∑_{k ∈ K} w_k (A z)_k ^ 2 / r_k` for all `z`. Then
`(zᵀ A z) (wᵀ A w) ≤ (wᵀ A z) ^ 2` for all `z` (`rcs_of_perron`).

This is Brändén–Leake, *Lorentzian polynomials on cones*, arXiv:2304.13203v2, Lemma 2.8,
for the cone `ℝⁿ_{>0}`. The proof uses a maximum principle in place of the
Perron–Frobenius theorem:

- scale by `c k = √(w k / r k)` on `K` and `c k = 0` off `K`, so that
  `S = diag(c) A diag(c)` satisfies `S v = v` for `v = c ⊙ r`, and (★) reads
  `ξ ⬝ S ξ ≤ ‖S ξ‖²` (`rcs_of_perron_scaled`);
- by the spectral theorem, `‖v‖² S - v vᵀ` is negative semidefinite as soon as it has no
  eigenvector for a positive eigenvalue (`dotProduct_mulVec_nonpos_of_eigen`);
- such an eigenvector `φ` is orthogonal to `v` and satisfies `S φ = λ φ` with `λ ≥ 1`; in the
  original coordinates `z = c ⊙ φ`, the ratio `z / w` is then constant on `K` by the maximum
  principle along `Relation.ReflTransGen` (`perron_maxPrinciple`), hence `φ = 0`.
-/

public section

open Matrix

namespace Parking

/-- **Spectral helper.** A real symmetric matrix that has no eigenvector for a positive
eigenvalue is negative semidefinite. -/
theorem dotProduct_mulVec_nonpos_of_eigen {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (h : ∀ (φ : Fin n → ℝ) (μ : ℝ), M *ᵥ φ = μ • φ → 0 < μ → φ = 0)
    (ξ : Fin n → ℝ) : ξ ⬝ᵥ (M *ᵥ ξ) ≤ 0 := by
  have hN : (-M).IsHermitian := isHermitian_iff_isSymm.mpr hM.neg
  have hpsd : (-M).PosSemidef := by
    rw [hN.posSemidef_iff_eigenvalues_nonneg, Pi.le_def]
    intro j
    by_contra hj
    have hj' : hN.eigenvalues j < 0 := by simpa using hj
    have hv := hN.mulVec_eigenvectorBasis j
    have hne : (⇑(hN.eigenvectorBasis j) : Fin n → ℝ) ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hN.eigenvectorBasis.orthonormal.ne_zero j)
    apply hne
    refine h _ (-hN.eigenvalues j) ?_ (neg_pos.2 hj')
    rw [neg_mulVec] at hv
    rw [neg_smul, ← hv, neg_neg]
  have := hpsd.dotProduct_mulVec_nonneg ξ
  rw [star_trivial, neg_mulVec, dotProduct_neg] at this
  linarith

/-- The vector `A w` is nonnegative when `A` and `w` are. -/
theorem mulVec_nonneg_of_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hA0 : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 ≤ w i) (k : Fin n) : 0 ≤ (A *ᵥ w) k := by
  show 0 ≤ ∑ l, A k l * w l
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hA0 k l) (hw l)

/-- If `A ≥ 0`, `w > 0` and `(A w)_k = 0`, then the row `k` of `A` vanishes. -/
theorem row_eq_zero_of_mulVec_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hA0 : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < w i) {k : Fin n} (hk : (A *ᵥ w) k = 0)
    (l : Fin n) : A k l = 0 := by
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ A k i * w i := fun i _ => mul_nonneg (hA0 k i) (hw i).le
  have hsum : ∑ i, A k i * w i = 0 := hk
  rcases mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum l (Finset.mem_univ l))
    with h | h
  · exact h
  · exact absurd h (hw l).ne'

/-- **Maximum principle.** Let `A ≥ 0`, `w > 0`, `r = A w`, with the graph `{A a b > 0}`
connecting any two points of `{r > 0}`. Let `z` vanish off `{r > 0}`, be orthogonal to `r`, and
satisfy `w_k (A z)_k = λ r_k z_k` with `λ ≥ 1`. Then `z ≤ 0`.

At a maximizer of `z / w`, where the maximum `H` is positive, the equation forces `z = H w`
at every neighbour; by connectivity `z = H w` on `{r > 0}`, which contradicts `r ⬝ z = 0`. -/
theorem perron_maxPrinciple {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hA0 : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < w i)
    (hconn : ∀ i j, 0 < (A *ᵥ w) i → 0 < (A *ᵥ w) j →
      Relation.ReflTransGen (fun a b => 0 < A a b) i j)
    (z : Fin n → ℝ) (lam : ℝ) (hlam : 1 ≤ lam)
    (heig : ∀ k, w k * (A *ᵥ z) k = lam * (A *ᵥ w) k * z k)
    (hzK : ∀ k, (A *ᵥ w) k = 0 → z k = 0) (horth : (A *ᵥ w) ⬝ᵥ z = 0) (k : Fin n) :
    z k ≤ 0 := by
  by_contra hk
  push Not at hk
  have hr0 := mulVec_nonneg_of_nonneg A w hA0 fun i => (hw i).le
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => z j / w j)
    ⟨k, Finset.mem_univ k⟩
  have hm' : ∀ l, z l / w l ≤ z m / w m := fun l => hm l (Finset.mem_univ l)
  obtain ⟨H, hH⟩ : ∃ H, H = z m / w m := ⟨_, rfl⟩
  rw [← hH] at hm'
  have hle : ∀ l, z l ≤ H * w l := fun l => (div_le_iff₀ (hw l)).mp (hm' l)
  have hHpos : 0 < H := (div_pos hk (hw k)).trans_le (hm' k)
  have hzm : z m = H * w m := by rw [hH, div_mul_cancel₀ _ (hw m).ne']
  -- a point where `z = H w` lies in `{r > 0}`
  have hpos : ∀ j, z j = H * w j → 0 < (A *ᵥ w) j := by
    intro j hj
    rcases (hr0 j).lt_or_eq with h | h
    · exact h
    · have := hzK j h.symm
      rw [hj] at this
      exact absurd this (mul_pos hHpos (hw j)).ne'
  -- the maximum propagates along the edges of `A`
  have step : ∀ j l, z j = H * w j → 0 < A j l → z l = H * w l := by
    intro j l hj hjl
    have hrj := hpos j hj
    have h2 : (A *ᵥ z) j = lam * (A *ᵥ w) j * H := by
      have h1 := heig j
      rw [hj] at h1
      apply mul_left_cancel₀ (hw j).ne'
      rw [h1]
      ring
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ A j i * (H * w i - z i) :=
      fun i _ => mul_nonneg (hA0 j i) (sub_nonneg.2 (hle i))
    have hsum : ∑ i, A j i * (H * w i - z i) = -((lam - 1) * H * (A *ᵥ w) j) := by
      have e1 : ∑ i, A j i * (H * w i - z i) = H * (A *ᵥ w) j - (A *ᵥ z) j := by
        show _ = H * ∑ i, A j i * w i - ∑ i, A j i * z i
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e1, h2]
      ring
    have h3 : 0 ≤ (lam - 1) * H * (A *ᵥ w) j :=
      mul_nonneg (mul_nonneg (sub_nonneg.2 hlam) hHpos.le) hrj.le
    have hzero : ∑ i, A j i * (H * w i - z i) = 0 :=
      le_antisymm (by rw [hsum]; exact neg_nonpos.2 h3) (Finset.sum_nonneg hnn)
    rcases mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero l
      (Finset.mem_univ l)) with h | h
    · exact absurd h hjl.ne'
    · linarith
  have reach : ∀ j, Relation.ReflTransGen (fun a b => 0 < A a b) m j → z j = H * w j := by
    intro j hj
    induction hj with
    | refl => exact hzm
    | tail _ hbc ih => exact step _ _ ih hbc
  have hrm := hpos m hzm
  have hall : ∀ j, (A *ᵥ w) j * z j = H * ((A *ᵥ w) j * w j) := by
    intro j
    rcases (hr0 j).lt_or_eq with h | h
    · rw [reach j (hconn m j hrm h)]
      ring
    · rw [← h]
      ring
  have hdot : (A *ᵥ w) ⬝ᵥ z = H * ((A *ᵥ w) ⬝ᵥ w) := by
    show ∑ j, (A *ᵥ w) j * z j = H * ∑ j, (A *ᵥ w) j * w j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hall j
  have hpos' : 0 < (A *ᵥ w) ⬝ᵥ w :=
    Finset.sum_pos' (fun i _ => mul_nonneg (hr0 i) (hw i).le)
      ⟨m, Finset.mem_univ m, mul_pos hrm (hw m)⟩
  rw [horth] at hdot
  have := mul_pos hHpos hpos'
  linarith

/-- The matrix `diag(c) A diag(c)` acts by `(diag(c) A diag(c) ξ)_k = c_k (A (c ⊙ ξ))_k`. -/
theorem scaledMatrix_mulVec_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c ξ : Fin n → ℝ)
    (k : Fin n) :
    (of (fun k l => c k * A k l * c l) *ᵥ ξ) k = c k * (A *ᵥ fun l => c l * ξ l) k := by
  show ∑ l, c k * A k l * c l * ξ l = c k * ∑ l, A k l * (c l * ξ l)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The quadratic form of `diag(c) A diag(c)` at `ξ` is that of `A` at `c ⊙ ξ`. -/
theorem dotProduct_scaledMatrix_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (c ξ : Fin n → ℝ) :
    ξ ⬝ᵥ (of (fun k l => c k * A k l * c l) *ᵥ ξ) =
      (fun l => c l * ξ l) ⬝ᵥ (A *ᵥ fun l => c l * ξ l) := by
  show ∑ k, ξ k * (of (fun k l => c k * A k l * c l) *ᵥ ξ) k =
    ∑ k, c k * ξ k * (A *ᵥ fun l => c l * ξ l) k
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [scaledMatrix_mulVec_apply]
  ring

/-- **The Perron step in scaled coordinates.** Under the hypotheses of `rcs_of_perron`, let
`c` satisfy `c_k ^ 2 r_k = w_k` where `r_k = (A w)_k > 0`, and `c_k = 0` elsewhere. Then
`S = diag(c) A diag(c)` and `v = c ⊙ r` satisfy `(ξ ⬝ S ξ) ‖v‖² ≤ (v ⬝ ξ)²` for every `ξ`,
that is, `S - v vᵀ / ‖v‖²` is negative semidefinite. -/
theorem rcs_of_perron_scaled {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w c : Fin n → ℝ)
    (hA : A.IsSymm) (hA0 : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < w i)
    (hconn : ∀ i j, 0 < (A *ᵥ w) i → 0 < (A *ᵥ w) j →
      Relation.ReflTransGen (fun a b => 0 < A a b) i j)
    (hstar : ∀ z, z ⬝ᵥ (A *ᵥ z) ≤
      ∑ k, if 0 < (A *ᵥ w) k then w k * (A *ᵥ z) k ^ 2 / (A *ᵥ w) k else 0)
    (hcK : ∀ k, 0 < (A *ᵥ w) k → c k ^ 2 * (A *ᵥ w) k = w k)
    (hc0 : ∀ k, ¬ 0 < (A *ᵥ w) k → c k = 0)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S = of fun k l => c k * A k l * c l)
    (v : Fin n → ℝ) (hv : v = fun k => c k * (A *ᵥ w) k) (ξ : Fin n → ℝ) :
    (ξ ⬝ᵥ (S *ᵥ ξ)) * (v ⬝ᵥ v) ≤ (v ⬝ᵥ ξ) ^ 2 := by
  have hr0 := mulVec_nonneg_of_nonneg A w hA0 fun i => (hw i).le
  have hrow : ∀ k l, ¬ 0 < (A *ᵥ w) k → A k l = 0 := fun k l hk =>
    row_eq_zero_of_mulVec_eq_zero A w hA0 hw (le_antisymm (not_lt.mp hk) (hr0 k)) l
  have hcol : ∀ k l, ¬ 0 < (A *ᵥ w) l → A k l = 0 := fun k l hl => by
    rw [← hA.apply k l]
    exact hrow l k hl
  have hSmul : ∀ φ k, (S *ᵥ φ) k = c k * (A *ᵥ fun l => c l * φ l) k := by
    intro φ k
    rw [hS, scaledMatrix_mulVec_apply]
  have hSsymm : S.IsSymm := by
    rw [hS]
    refine IsSymm.ext fun i j => ?_
    show c j * A j i * c i = c i * A i j * c j
    rw [hA.apply i j]
    ring
  have hSv : S *ᵥ v = v := by
    funext k
    rw [hSmul, hv]
    congr 1
    show ∑ l, A k l * (c l * (c l * (A *ᵥ w) l)) = ∑ l, A k l * w l
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : 0 < (A *ᵥ w) l
    · rw [← hcK l hl]
      ring
    · rw [hcol k l hl, zero_mul, zero_mul]
  -- (★) in the scaled coordinates
  have hstar' : ∀ φ, φ ⬝ᵥ (S *ᵥ φ) ≤ (S *ᵥ φ) ⬝ᵥ (S *ᵥ φ) := by
    intro φ
    rw [hS, dotProduct_scaledMatrix_mulVec, ← hS]
    refine (hstar _).trans_eq ?_
    show _ = ∑ k, (S *ᵥ φ) k * (S *ᵥ φ) k
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hSmul]
    split_ifs with hk
    · rw [← hcK k hk]
      field_simp
    · rw [hc0 k hk]
      ring
  -- the matrix `N S - v vᵀ`, with `N = v ⬝ v`
  obtain ⟨N, hN⟩ : ∃ N, N = v ⬝ᵥ v := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by
    rw [hN]
    exact Finset.sum_nonneg fun k _ => mul_self_nonneg (v k)
  have hvS : ∀ φ, v ⬝ᵥ (S *ᵥ φ) = v ⬝ᵥ φ := by
    intro φ
    rw [dotProduct_mulVec, ← mulVec_transpose, hSsymm.eq, hSv]
  set M : Matrix (Fin n) (Fin n) ℝ := of fun k l => N * S k l - v k * v l with hM
  have hMvec : ∀ φ, M *ᵥ φ = N • (S *ᵥ φ) - (v ⬝ᵥ φ) • v := by
    intro φ
    funext k
    show ∑ l, (N * S k l - v k * v l) * φ l = N * ∑ l, S k l * φ l - (∑ l, v l * φ l) * v k
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hMsymm : M.IsSymm := by
    refine IsSymm.ext fun i j => ?_
    show N * S j i - v j * v i = N * S i j - v i * v j
    rw [hSsymm.apply i j]
    ring
  -- `N S - v vᵀ` has no eigenvector for a positive eigenvalue
  have heig : ∀ (φ : Fin n → ℝ) (μ : ℝ), M *ᵥ φ = μ • φ → 0 < μ → φ = 0 := by
    intro φ μ hφ hμ
    have horth : v ⬝ᵥ φ = 0 := by
      have h1 := congrArg (v ⬝ᵥ ·) hφ
      simp only [hMvec, dotProduct_sub, dotProduct_smul, smul_eq_mul, hvS] at h1
      have h2 : μ * (v ⬝ᵥ φ) = 0 := by
        rw [← h1, ← hN]
        ring
      exact (mul_eq_zero.mp h2).resolve_left hμ.ne'
    have hSφ : ∀ k, N * (S *ᵥ φ) k = μ * φ k := by
      intro k
      have h1 := congrFun hφ k
      rw [hMvec, horth] at h1
      simpa using h1
    rcases hN0.eq_or_lt with hN0 | hNpos
    · funext k
      have h1 := hSφ k
      rw [← hN0, zero_mul] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hμ.ne'
    -- `S φ = λ φ` with `λ = μ / N > 0`
    obtain ⟨lam, hlam⟩ : ∃ lam, lam = μ / N := ⟨_, rfl⟩
    have hlampos : 0 < lam := by
      rw [hlam]
      exact div_pos hμ hNpos
    have hSvec : S *ᵥ φ = lam • φ := by
      funext k
      rw [Pi.smul_apply, smul_eq_mul, hlam, div_mul_eq_mul_div, eq_div_iff hNpos.ne', mul_comm]
      exact hSφ k
    by_contra hφ0
    -- `λ ≥ 1` from (★)
    have hpp : 0 < φ ⬝ᵥ φ := by
      rcases (Finset.sum_nonneg fun k _ => mul_self_nonneg (φ k) :
          0 ≤ φ ⬝ᵥ φ).eq_or_lt with h | h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hφ0
      · exact h
    have hlam1 : 1 ≤ lam := by
      have hs := hstar' φ
      rw [hSvec, dotProduct_smul, smul_dotProduct, dotProduct_smul] at hs
      simp only [smul_eq_mul] at hs
      by_contra h
      push Not at h
      have h4 : lam * (φ ⬝ᵥ φ) < φ ⬝ᵥ φ := mul_lt_of_lt_one_left hpp h
      have h5 : lam * (lam * (φ ⬝ᵥ φ)) < lam * (φ ⬝ᵥ φ) := mul_lt_mul_of_pos_left h4 hlampos
      linarith
    -- back to the coordinates `z = c ⊙ φ`
    have hcφ : ∀ k, c k * (A *ᵥ fun l => c l * φ l) k = lam * φ k := by
      intro k
      rw [← hSmul, hSvec]
      rfl
    have hAz : ∀ (y : Fin n → ℝ) k, ¬ 0 < (A *ᵥ w) k → (A *ᵥ y) k = 0 := by
      intro y k hk
      show ∑ l, A k l * y l = 0
      exact Finset.sum_eq_zero fun l _ => by rw [hrow k l hk, zero_mul]
    have hz_eig : ∀ k, w k * (A *ᵥ fun l => c l * φ l) k =
        lam * (A *ᵥ w) k * (c k * φ k) := by
      intro k
      by_cases hk : 0 < (A *ᵥ w) k
      · rw [← hcK k hk]
        calc c k ^ 2 * (A *ᵥ w) k * (A *ᵥ fun l => c l * φ l) k
            = (A *ᵥ w) k * c k * (c k * (A *ᵥ fun l => c l * φ l) k) := by ring
          _ = (A *ᵥ w) k * c k * (lam * φ k) := by rw [hcφ]
          _ = lam * (A *ᵥ w) k * (c k * φ k) := by ring
      · rw [hAz _ k hk, le_antisymm (not_lt.mp hk) (hr0 k)]
        ring
    have hzK : ∀ k, (A *ᵥ w) k = 0 → c k * φ k = 0 := by
      intro k hk
      rw [hc0 k (by rw [hk]; exact lt_irrefl 0), zero_mul]
    have horth_z : (A *ᵥ w) ⬝ᵥ (fun l => c l * φ l) = 0 := by
      rw [← horth, hv]
      show ∑ k, (A *ᵥ w) k * (c k * φ k) = ∑ k, c k * (A *ᵥ w) k * φ k
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hle := perron_maxPrinciple A w hA0 hw hconn (fun l => c l * φ l) lam hlam1 hz_eig hzK
      horth_z
    have hge := perron_maxPrinciple A w hA0 hw hconn (-fun l => c l * φ l) lam hlam1
      (fun k => by
        rw [mulVec_neg, Pi.neg_apply, Pi.neg_apply, mul_neg, hz_eig k]
        ring)
      (fun k hk => by rw [Pi.neg_apply, hzK k hk, neg_zero])
      (by rw [dotProduct_neg, horth_z, neg_zero])
    have hz0 : (fun l => c l * φ l) = 0 := by
      funext l
      have h1 := hle l
      have h2 := hge l
      rw [Pi.neg_apply] at h2
      simp only [Pi.zero_apply]
      linarith
    apply hφ0
    funext k
    have h1 := hcφ k
    rw [hz0, mulVec_zero, Pi.zero_apply, mul_zero] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hlampos.ne'
  -- conclusion
  have hneg := dotProduct_mulVec_nonpos_of_eigen M hMsymm heig ξ
  rw [hMvec, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    dotProduct_comm ξ v] at hneg
  rw [← hN]
  linarith

/-- **Perron step** (Brändén–Leake, arXiv:2304.13203v2, Lemma 2.8, for the cone `ℝⁿ_{>0}`).
Let `A` be a symmetric matrix with nonnegative entries and `w > 0`. Assume that the graph
`{A a b > 0}` connects any two indices `i, j` with `(A w)_i, (A w)_j > 0`, and
(★) `z ⬝ A z ≤ ∑_{(A w)_k > 0} w_k (A z)_k ^ 2 / (A w)_k` for all `z`. Then
`(z ⬝ A z) (w ⬝ A w) ≤ (w ⬝ A z) ^ 2` for all `z`. -/
theorem rcs_of_perron {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hA : A.IsSymm) (hA0 : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < w i)
    (hconn : ∀ i j, 0 < (A *ᵥ w) i → 0 < (A *ᵥ w) j →
      Relation.ReflTransGen (fun a b => 0 < A a b) i j)
    (hstar : ∀ z, z ⬝ᵥ (A *ᵥ z) ≤
      ∑ k, if 0 < (A *ᵥ w) k then w k * (A *ᵥ z) k ^ 2 / (A *ᵥ w) k else 0) :
    ∀ z, (z ⬝ᵥ (A *ᵥ z)) * (w ⬝ᵥ (A *ᵥ w)) ≤ (w ⬝ᵥ (A *ᵥ z)) ^ 2 := by
  intro z
  have hr0 := mulVec_nonneg_of_nonneg A w hA0 fun i => (hw i).le
  have hrow : ∀ k l, ¬ 0 < (A *ᵥ w) k → A k l = 0 := fun k l hk =>
    row_eq_zero_of_mulVec_eq_zero A w hA0 hw (le_antisymm (not_lt.mp hk) (hr0 k)) l
  have hcol : ∀ k l, ¬ 0 < (A *ᵥ w) l → A k l = 0 := fun k l hl => by
    rw [← hA.apply k l]
    exact hrow l k hl
  have hAz : ∀ (y : Fin n → ℝ) k, ¬ 0 < (A *ᵥ w) k → (A *ᵥ y) k = 0 := by
    intro y k hk
    show ∑ l, A k l * y l = 0
    exact Finset.sum_eq_zero fun l _ => by rw [hrow k l hk, zero_mul]
  -- the scaling `c k = √(w k / (A w)_k)` on the support of `A w`, and `0` elsewhere
  obtain ⟨c, hcK, hc0⟩ : ∃ c : Fin n → ℝ, (∀ k, 0 < (A *ᵥ w) k → c k ^ 2 * (A *ᵥ w) k = w k) ∧
      ∀ k, ¬ 0 < (A *ᵥ w) k → c k = 0 := by
    refine ⟨fun k => if 0 < (A *ᵥ w) k then √(w k / (A *ᵥ w) k) else 0, fun k hk => ?_,
      fun k hk => ?_⟩
    · simp only [hk, ↓reduceIte]
      rw [Real.sq_sqrt (div_nonneg (hw k).le hk.le), div_mul_cancel₀ _ hk.ne']
    · simp only [hk, ↓reduceIte]
  have hcne : ∀ k, 0 < (A *ᵥ w) k → c k ≠ 0 := by
    intro k hk h
    have := hcK k hk
    rw [h] at this
    have := hw k
    simp_all
  have key := rcs_of_perron_scaled A w c hA hA0 hw hconn hstar hcK hc0 _ rfl _ rfl
    (fun k => z k / c k)
  -- translate back to `A`
  have hAz' : (A *ᵥ fun l => c l * (z l / c l)) = A *ᵥ z := by
    funext k
    show ∑ l, A k l * (c l * (z l / c l)) = ∑ l, A k l * z l
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : 0 < (A *ᵥ w) l
    · rw [mul_div_cancel₀ _ (hcne l hl)]
    · rw [hcol k l hl, zero_mul, zero_mul]
  have e1 : (fun k => z k / c k) ⬝ᵥ (of (fun k l => c k * A k l * c l) *ᵥ fun k => z k / c k) =
      z ⬝ᵥ (A *ᵥ z) := by
    rw [dotProduct_scaledMatrix_mulVec, hAz']
    show ∑ k, c k * (z k / c k) * (A *ᵥ z) k = ∑ k, z k * (A *ᵥ z) k
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : 0 < (A *ᵥ w) k
    · rw [mul_div_cancel₀ _ (hcne k hk)]
    · rw [hAz z k hk, mul_zero, mul_zero]
  have e2 : (fun k => c k * (A *ᵥ w) k) ⬝ᵥ (fun k => c k * (A *ᵥ w) k) = w ⬝ᵥ (A *ᵥ w) := by
    show ∑ k, c k * (A *ᵥ w) k * (c k * (A *ᵥ w) k) = ∑ k, w k * (A *ᵥ w) k
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : 0 < (A *ᵥ w) k
    · rw [← hcK k hk]
      ring
    · rw [le_antisymm (not_lt.mp hk) (hr0 k)]
      ring
  have e3 : (fun k => c k * (A *ᵥ w) k) ⬝ᵥ (fun k => z k / c k) = w ⬝ᵥ (A *ᵥ z) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq]
    show ∑ k, c k * (A *ᵥ w) k * (z k / c k) = ∑ k, (A *ᵥ w) k * z k
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : 0 < (A *ᵥ w) k
    · rw [mul_comm (c k), mul_assoc, mul_div_cancel₀ _ (hcne k hk)]
    · rw [le_antisymm (not_lt.mp hk) (hr0 k)]
      ring
  rw [e1, e2, e3] at key
  exact key

end Parking
