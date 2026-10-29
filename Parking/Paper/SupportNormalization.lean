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

public import Parking.Paper.StrongCompleteEquivalence
public import Parking.SupportGenFunCLC

/-!
# M-convex support and factorial support normalization

The proof of the support theorem uses the down-set of the polynomial support.
Reverse Cauchy–Schwarz for coordinate derivatives gives its local augmentation
property. A contraction induction promotes this to full augmentation, and the
homogeneous top layer has the M-convex exchange property. This is an internal
alternative to the translated c-Rayleigh proof of Brändén–Huh, Theorem 2.23.
-/

@[expose] public section

open MvPolynomial

namespace Parking

/-- The downward closure of the exponent support. -/
def supportDown {d : ℕ} (f : MvPolynomial (Fin d) ℝ) : Set (Fin d →₀ ℕ) :=
  {α | ∃ β ∈ f.support, α ≤ β}

theorem supportDown_lower {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    {α β : Fin d →₀ ℕ} (hβ : β ∈ supportDown f) (hα : α ≤ β) :
    α ∈ supportDown f := by
  obtain ⟨γ, hγ, hβγ⟩ := hβ
  exact ⟨γ, hγ, hα.trans hβγ⟩

theorem mem_support_pderiv_iff {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (i : Fin d) (α : Fin d →₀ ℕ) :
    α ∈ (MvPolynomial.pderiv i f).support ↔ α + Finsupp.single i 1 ∈ f.support := by
  simp only [MvPolynomial.mem_support_iff, coeff_pderiv, ne_eq, mul_eq_zero]
  have h : (α i + 1 : ℝ) ≠ 0 := by positivity
  simp [h]

theorem mem_supportDown_pderiv_iff {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (i : Fin d) (α : Fin d →₀ ℕ) :
    α ∈ supportDown (MvPolynomial.pderiv i f) ↔ α + Finsupp.single i 1 ∈ supportDown f := by
  constructor
  · rintro ⟨β, hβ, hαβ⟩
    exact ⟨β + Finsupp.single i 1, (mem_support_pderiv_iff i β).mp hβ,
      add_le_add hαβ le_rfl⟩
  · rintro ⟨β, hβ, hαβ⟩
    have hi : Finsupp.single i 1 ≤ β := le_trans (le_add_left le_rfl) hαβ
    refine ⟨β - Finsupp.single i 1, ?_, ?_⟩
    · rw [mem_support_pderiv_iff, tsub_add_cancel_of_le hi]
      exact hβ
    · exact (le_tsub_iff_right hi).mpr hαβ

theorem zero_mem_supportDown_iff {d : ℕ} {f : MvPolynomial (Fin d) ℝ} :
    0 ∈ supportDown f ↔ f ≠ 0 := by
  constructor
  · rintro ⟨β, hβ, _⟩ hf
    simp [hf] at hβ
  · intro hf
    obtain ⟨β, hβ⟩ := Finset.nonempty_iff_ne_empty.mpr
      (fun h => hf (MvPolynomial.support_eq_empty.mp h))
    exact ⟨β, hβ, zero_le⟩

theorem single_mem_supportDown_iff {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (i : Fin d) :
    Finsupp.single i 1 ∈ supportDown f ↔ MvPolynomial.pderiv i f ≠ 0 := by
  simpa using (mem_supportDown_pderiv_iff (f := f) i 0).symm.trans
    zero_mem_supportDown_iff

theorem two_single_mem_supportDown_iff {d : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (i j : Fin d) :
    Finsupp.single i 1 + Finsupp.single j 1 ∈ supportDown f ↔
      MvPolynomial.pderiv i (MvPolynomial.pderiv j f) ≠ 0 := by
  rw [← mem_supportDown_pderiv_iff, single_mem_supportDown_iff]

/-- A local augmentation property of a downward closed exponent set. -/
def SupportLocal {d : ℕ} (J : Set (Fin d →₀ ℕ)) : Prop :=
  ∀ γ i j k, γ + Finsupp.single i 1 ∈ J →
    γ + Finsupp.single j 1 + Finsupp.single k 1 ∈ J →
    γ + Finsupp.single i 1 + Finsupp.single j 1 ∈ J ∨
    γ + Finsupp.single i 1 + Finsupp.single k 1 ∈ J

/-- Contraction preserves downward closure. -/
theorem lower_contract {d : ℕ} {J : Set (Fin d →₀ ℕ)}
    (hJ : ∀ {α β}, β ∈ J → α ≤ β → α ∈ J) (i : Fin d) :
    ∀ {α β}, β + Finsupp.single i 1 ∈ J → α ≤ β →
      α + Finsupp.single i 1 ∈ J :=
  fun hβ hα => hJ hβ (add_le_add hα le_rfl)

theorem SupportLocal.contract {d : ℕ} {J : Set (Fin d →₀ ℕ)}
    (hJ : SupportLocal J) (i : Fin d) :
    SupportLocal {α | α + Finsupp.single i 1 ∈ J} := by
  intro γ a b c ha hbc
  have h := hJ (γ + Finsupp.single i 1) a b c
    (by simpa only [Set.mem_ofPred_eq, add_assoc, add_comm, add_left_comm] using ha)
    (by simpa only [Set.mem_ofPred_eq, add_assoc, add_comm, add_left_comm] using hbc)
  simpa only [Set.mem_ofPred_eq, add_assoc, add_comm, add_left_comm] using h

/-- Local augmentation on all contractions implies the full augmentation axiom.
This elementary induction is the discrete step in the support theorem. -/
theorem augmentation_of_supportLocal {d : ℕ} {J : Set (Fin d →₀ ℕ)}
    (hJ : ∀ {α β}, β ∈ J → α ≤ β → α ∈ J) (hloc : SupportLocal J)
    {α β : Fin d →₀ ℕ} (hα : α ∈ J) (hβ : β ∈ J)
    (hdeg : α.degree < β.degree) :
    ∃ j, α j < β j ∧ α + Finsupp.single j 1 ∈ J := by
  classical
  have aux : ∀ n (J : Set (Fin d →₀ ℕ)),
      (∀ {α β}, β ∈ J → α ≤ β → α ∈ J) → SupportLocal J →
      ∀ α β, α.degree + β.degree = n → α ∈ J → β ∈ J →
      α.degree < β.degree → ∃ j, α j < β j ∧ α + Finsupp.single j 1 ∈ J := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J hJ hloc α β hn hα hβ hdeg
      by_cases hshare : ∃ i, 0 < α i ∧ 0 < β i
      · obtain ⟨i, hiα, hiβ⟩ := hshare
        obtain ⟨a, rfl⟩ := le_iff_exists_add'.mp
          (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hiα.ne'))
        obtain ⟨b, rfl⟩ := le_iff_exists_add'.mp
          (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hiβ.ne'))
        simp only [map_add, Finsupp.degree_single] at hn hdeg
        obtain ⟨j, hj, hmem⟩ := ih (a.degree + b.degree) (by omega)
          {γ | γ + Finsupp.single i 1 ∈ J} (lower_contract hJ i) (hloc.contract i)
          a b rfl hα hβ (by omega)
        refine ⟨j, ?_, ?_⟩
        · simpa only [Finsupp.add_apply, add_lt_add_iff_right] using hj
        · simpa only [Set.mem_ofPred_eq, add_assoc, add_comm, add_left_comm] using hmem
      · have hdis : ∀ i, 0 < β i → α i = 0 := by
          intro i hi
          by_contra hαi
          exact hshare ⟨i, Nat.pos_of_ne_zero hαi, hi⟩
        by_cases hα0 : α = 0
        · subst α
          have hβ0 : β ≠ 0 := by intro hb; simp [hb] at hdeg
          obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hβ0
          refine ⟨j, by simpa using Nat.pos_of_ne_zero hj, ?_⟩
          simpa using hJ hβ (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj))
        · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hα0
          obtain ⟨a, haeq⟩ := le_iff_exists_add'.mp
            (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))
          have ha : a ∈ J := hJ hα (by rw [haeq]; exact le_add_right le_rfl)
          have hda : α.degree = a.degree + 1 := by rw [haeq, map_add, Finsupp.degree_single]
          obtain ⟨j, hj, haj⟩ := ih (a.degree + β.degree) (by omega)
            J hJ hloc a β rfl ha hβ (by omega)
          have hβj : 0 < β j := lt_of_le_of_lt (Nat.zero_le _) hj
          have hαj : α j = 0 := hdis j hβj
          have hsingle : Finsupp.single j 1 ≤ β := Finsupp.single_le_iff.mpr hβj
          obtain ⟨b, hbeq⟩ := le_iff_exists_add'.mp hsingle
          have hdb : β.degree = b.degree + 1 := by rw [hbeq, map_add, Finsupp.degree_single]
          have hbmem : b + Finsupp.single j 1 ∈ J := by rw [← hbeq]; exact hβ
          obtain ⟨k, hk, hak⟩ := ih (a.degree + b.degree) (by omega)
            {γ | γ + Finsupp.single j 1 ∈ J} (lower_contract hJ j) (hloc.contract j)
            a b rfl haj hbmem (by omega)
          have hβk : 0 < β k := lt_of_lt_of_le
            (lt_of_le_of_lt (Nat.zero_le _) hk) (by rw [hbeq]; exact Nat.le_add_right _ _)
          have hαk : α k = 0 := hdis k hβk
          have haloc : a + Finsupp.single i 1 ∈ J := by rw [← haeq]; exact hα
          have hmix : a + Finsupp.single j 1 + Finsupp.single k 1 ∈ J := by
            simpa only [Set.mem_ofPred_eq, add_assoc, add_comm, add_left_comm] using hak
          rcases hloc a i j k haloc hmix with h | h
          · exact ⟨j, by simpa [hαj] using hβj, by simpa only [← haeq] using h⟩
          · exact ⟨k, by simpa [hαk] using hβk, by simpa only [← haeq] using h⟩
  exact aux (α.degree + β.degree) J hJ hloc α β rfl hα hβ hdeg


/-- In a symmetric reverse-Cauchy–Schwarz form, a vector with nonnegative
square and a positive mixed product cannot be orthogonal to a positive vector. -/
theorem bilin_mixed_ne_zero_of_revCS {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hs : ∀ x y, B x y = B y x)
    (hr : ∀ x y, 0 < B x x → B x x * B y y ≤ (B x y) ^ 2) {u v w : E}
    (hu : 0 ≤ B u u) (hv : 0 < B v v) (hw : 0 ≤ B w w)
    (huw : 0 < B u w) : B u v ≠ 0 := by
  intro huv
  have hvu : B v u = 0 := by rw [hs, huv]
  let t : ℝ := ((B v w) ^ 2 + 1) / (2 * B u w * B v v)
  have ht : 0 < t := div_pos (by positivity) (by positivity)
  have hq : 2 * t * B u w ≤ B (t • u + w) (t • u + w) := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    rw [hs w u]
    nlinarith [mul_nonneg (sq_nonneg t) hu]
  have h := hr v (t • u + w) hv
  have hmix : B v (t • u + w) = B v w := by
    simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
      hvu, mul_zero, zero_add]
  rw [hmix] at h
  have heq : B v v * (2 * t * B u w) = (B v w) ^ 2 + 1 := by
    dsimp [t]
    field_simp
  have hh := (mul_le_mul_of_nonneg_left hq hv.le).trans h
  rw [heq] at hh
  linarith

theorem degree_le_of_mem_supportDown {d m : ℕ} {f : MvPolynomial (Fin d) ℝ}
    (hhom : f.IsHomogeneous m) {α : Fin d →₀ ℕ} (hα : α ∈ supportDown f) :
    α.degree ≤ m := by
  obtain ⟨β, hβ, hle⟩ := hα
  have hdeg : β.degree = m := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hhom (mem_support_iff.mp hβ)
  exact (Finsupp.degree_mono hle).trans_eq hdeg

/-- The Hessian obstruction that forces local support augmentation. -/
theorem StronglyLogConcave.support_local_zero {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m) (i j k : Fin d)
    (hi : Finsupp.single i 1 ∈ supportDown f)
    (hjk : Finsupp.single j 1 + Finsupp.single k 1 ∈ supportDown f) :
    Finsupp.single i 1 + Finsupp.single j 1 ∈ supportDown f ∨
    Finsupp.single i 1 + Finsupp.single k 1 ∈ supportDown f := by
  classical
  have hm : 2 ≤ m := by
    have h := degree_le_of_mem_supportDown hhom hjk
    simpa only [map_add, Finsupp.degree_single] using h
  rw [single_mem_supportDown_iff] at hi
  rw [two_single_mem_supportDown_iff] at hjk ⊢
  rw [two_single_mem_supportDown_iff]
  by_contra h
  push Not at h
  let B := polynomialHessian f (1 : Fin d → ℝ)
  let e : Fin d → (Fin d → ℝ) := fun a => Pi.single a 1
  have hpos : (1 : Fin d → ℝ) ∈ posOrthant d := fun _ => zero_lt_one
  have hentry (a b : Fin d) : B (e a) (e b) = eval 1 (MvPolynomial.pderiv a (MvPolynomial.pderiv b f)) := by
    simp only [B, e, polynomialHessian_apply, dirDeriv_single, Derivation.coeFn_coe]
  have hnonneg (a b : Fin d) : 0 ≤ B (e a) (e b) := by
    rw [hentry]
    by_cases hz : MvPolynomial.pderiv a (MvPolynomial.pderiv b f) = 0
    · simp [hz]
    · exact (eval_pos_of_coeff_nonneg
        (coeff_pderiv_nonneg (coeff_pderiv_nonneg hf.1 b) a) hz hpos).le
  have hposjk : 0 < B (e j) (e k) := by
    rw [hentry]
    exact eval_pos_of_coeff_nonneg
      (coeff_pderiv_nonneg (coeff_pderiv_nonneg hf.1 k) j) hjk hpos
  have hv : 0 < B (e j + e k) (e j + e k) := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
    linarith [hnonneg j j, hnonneg k j, hnonneg k k]
  have hw : 0 ≤ B (1 : Fin d → ℝ) 1 := by
    rw [show B 1 1 = _ from polynomialHessian_self_self hhom 1]
    have hf0 : f ≠ 0 := by intro hz; simp [hz] at hi
    exact mul_nonneg (by positivity) (eval_pos_of_coeff_nonneg hf.1 hf0 hpos).le
  have hiw : 0 < B (e i) 1 := by
    rw [show B (e i) 1 = B 1 (e i) from polynomialHessian_symm f 1 _ _,
      show B 1 (e i) = _ from polynomialHessian_self_left hhom 1 (e i)]
    simp only [e, dirDeriv_single, Derivation.coeFn_coe]
    exact mul_pos (by exact_mod_cast (by omega : 0 < m - 1))
      (eval_pos_of_coeff_nonneg (coeff_pderiv_nonneg hf.1 i) hi hpos)
  have hne := bilin_mixed_ne_zero_of_revCS B (polynomialHessian_symm f 1)
    (hf.revCS_polynomialHessian hhom hm hpos) (hnonneg i i) hv hw hiw
  apply hne
  rw [LinearMap.BilinForm.add_right, hentry, hentry, h.1, h.2]
  simp


/-- Every contraction of the support down-set has the local augmentation property. -/
theorem StronglyLogConcave.supportLocal {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m) : SupportLocal (supportDown f) := by
  have aux : ∀ n, ∀ (m : ℕ) (f : MvPolynomial (Fin d) ℝ),
      StronglyLogConcave f → f.IsHomogeneous m →
      ∀ γ : Fin d →₀ ℕ, γ.degree = n → ∀ i j k,
      γ + Finsupp.single i 1 ∈ supportDown f →
      γ + Finsupp.single j 1 + Finsupp.single k 1 ∈ supportDown f →
      γ + Finsupp.single i 1 + Finsupp.single j 1 ∈ supportDown f ∨
      γ + Finsupp.single i 1 + Finsupp.single k 1 ∈ supportDown f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m f hf hhom γ hγ i j k hi hjk
      by_cases hγ0 : γ = 0
      · subst γ
        simpa only [zero_add] using hf.support_local_zero hhom i j k
          (by simpa only [zero_add] using hi) (by simpa only [zero_add] using hjk)
      · obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hγ0
        obtain ⟨δ, hδ⟩ := le_iff_exists_add'.mp
          (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr ha))
        have hdeg : δ.degree < n := by
          rw [hδ, map_add, Finsupp.degree_single] at hγ
          omega
        have hi' : δ + Finsupp.single i 1 ∈ supportDown (MvPolynomial.pderiv a f) := by
          rw [mem_supportDown_pderiv_iff]
          simpa only [hδ, add_assoc, add_comm, add_left_comm] using hi
        have hjk' : δ + Finsupp.single j 1 + Finsupp.single k 1 ∈
            supportDown (MvPolynomial.pderiv a f) := by
          rw [mem_supportDown_pderiv_iff]
          simpa only [hδ, add_assoc, add_comm, add_left_comm] using hjk
        have h := ih δ.degree hdeg (m - 1) (MvPolynomial.pderiv a f)
          (hf.pderiv a) hhom.pderiv δ rfl i j k hi' hjk'
        simp only [mem_supportDown_pderiv_iff] at h
        simpa only [hδ, add_assoc, add_comm, add_left_comm] using h
  intro γ i j k hi hjk
  exact aux γ.degree m f hf hhom γ rfl i j k hi hjk

/-- The homogeneous top layer of the down-set is the original support. -/
theorem mem_support_of_mem_supportDown {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hhom : f.IsHomogeneous m)
    {α : Fin d →₀ ℕ} (hα : α ∈ supportDown f) (hdeg : α.degree = m) :
    α ∈ f.support := by
  obtain ⟨β, hβ, hle⟩ := hα
  obtain ⟨δ, rfl⟩ := le_iff_exists_add.mp hle
  have hβdeg : (α + δ).degree = m := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hhom (mem_support_iff.mp hβ)
  rw [map_add, hdeg] at hβdeg
  have hδ : δ = 0 := (Finsupp.degree_eq_zero_iff δ).mp (by omega)
  simpa [hδ] using hβ

/-- **SLC implies M-convex support.** This is the exact homogeneous support
consequence in Brändén–Huh, Corollary 2.31, proved through support augmentation. -/
theorem StronglyLogConcave.isMConvex_support {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m) : IsMConvex (f.support : Set (Fin d →₀ ℕ)) := by
  intro α hα β hβ i hi
  have hdegα : α.degree = m := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hhom (mem_support_iff.mp hα)
  have hdegβ : β.degree = m := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hhom (mem_support_iff.mp hβ)
  have his : Finsupp.single i 1 ≤ α := Finsupp.single_le_iff.mpr (by omega)
  let γ := α - Finsupp.single i 1
  have hγα : γ + Finsupp.single i 1 = α := tsub_add_cancel_of_le his
  have hdegγ : γ.degree + 1 = m := by
    have h := congrArg Finsupp.degree hγα
    simpa only [map_add, Finsupp.degree_single, hdegα] using h
  have hγ : γ ∈ supportDown f := ⟨α, hα, tsub_le_self⟩
  obtain ⟨j, hj, hmem⟩ := augmentation_of_supportLocal
    (fun h hle => supportDown_lower h hle) (hf.supportLocal hhom)
    hγ ⟨β, hβ, le_rfl⟩ (by omega)
  have hji : j ≠ i := by
    intro heq
    subst j
    have hγi : γ i = α i - 1 := by simp [γ]
    omega
  have hj' : α j < β j := by
    simpa only [γ, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hji,
      Nat.sub_zero] using hj
  refine ⟨j, hj', mem_support_of_mem_supportDown hhom hmem ?_⟩
  simpa only [map_add, Finsupp.degree_single] using hdegγ

/-- Factorial normalization of the support preserves homogeneous strong
log-concavity. The support condition is derived from the input polynomial. -/
theorem StronglyLogConcave.supportGenFun_of_BH20 (hBH : BH20.SupportGenFunCLC)
    {d m : ℕ} {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m) : StronglyLogConcave (supportGenFun f.support) := by
  have hdeg : ∀ α ∈ f.support, α.degree = m := by
    intro α hα
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hhom (mem_support_iff.mp hα)
  by_cases he : f.support.Nonempty
  · exact (hBH d m f.support he hdeg
      (hf.isMConvex_support hhom)).stronglyLogConcave
  · have hz : f.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hz, supportGenFun_eq_zero_iff.mpr rfl]
    refine ⟨fun α => by simp, fun α => Or.inl ?_⟩
    simp [iteratedPDeriv]

/-- Unconditional factorial support normalization, using the proved
M-convex generating-polynomial citation theorem. -/
theorem StronglyLogConcave.supportGenFun {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m) : StronglyLogConcave (supportGenFun f.support) :=
  hf.supportGenFun_of_BH20 bh20_supportGenFunCLC hhom

end Parking

end
