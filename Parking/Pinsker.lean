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

public import Parking.Law
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Pinsker's inequality on a finite set

Pinsker's inequality `KL(P ‖ Q) ≥ 2 d_TV(P, Q)²`, with natural logarithm, for two
probability laws on a finite discrete space (`prop:decoupling`;
[PW25, Theorem 7.10]). Here `d_TV` is `Parking.tvDist` and `KL` is Mathlib's
`InformationTheory.klDiv`.

The proof reduces to two points. With `A = {x | Q(x) < P(x)}` one has
`d_TV(P, Q) = P(A) - Q(A)`, and the data processing inequality
`InformationTheory.klDiv_map_le` for the indicator of `A` bounds the binary divergence
`p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`, with `p = P(A)` and `q = Q(A)`, by
`KL(P ‖ Q)`. The binary inequality follows from the monotonicity of
`q ↦ -p log q - (1 - p) log (1 - q) - 2 (p - q)²` on `(0, p]`, whose derivative is
`(q - p) (2q - 1)² / (q (1 - q))`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace Parking

/-- The derivative of `q ↦ -p log q - (1 - p) log (1 - q) - 2 (p - q)²` on `(0, 1)`. -/
theorem hasDerivAt_pinskerAux (p : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => -(p * Real.log y) - (1 - p) * Real.log (1 - y) - 2 * (p - y) ^ 2)
      (-p / x + (1 - p) / (1 - x) + 4 * (p - x)) x := by
  have h1 := ((Real.hasDerivAt_log hx0.ne').const_mul p).neg
  have h2 := (((hasDerivAt_id' x).const_sub 1).log (by linarith : (1 : ℝ) - x ≠ 0)).const_mul
    (1 - p)
  have h3 := (((hasDerivAt_id' x).const_sub p).pow 2).const_mul 2
  convert (h1.sub h2).sub h3 using 1
  have : (1 : ℝ) - x ≠ 0 := by linarith
  field_simp
  ring

/-- Binary Pinsker inequality: for `0 < q ≤ p ≤ 1`,
`2 (p - q)² ≤ p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`. -/
theorem two_mul_sq_le_binaryKL {p q : ℝ} (hq : 0 < q) (hqp : q ≤ p) (hp : p ≤ 1) :
    2 * (p - q) ^ 2 ≤ p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  set G : ℝ → ℝ := fun y => -(p * Real.log y) - (1 - p) * Real.log (1 - y) - 2 * (p - y) ^ 2
    with hG
  have hp0 : 0 < p := hq.trans_le hqp
  have hcont : ContinuousOn G (Set.Ioc 0 p) := by
    have c1 : ContinuousOn (fun y : ℝ => p * Real.log y) (Set.Ioc 0 p) :=
      continuousOn_const.mul (continuousOn_id.log fun y hy => hy.1.ne')
    have c2 : ContinuousOn (fun y : ℝ => (1 - p) * Real.log (1 - y)) (Set.Ioc 0 p) := by
      rcases hp.lt_or_eq with hp1 | hp1
      · refine continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).log ?_)
        intro y hy
        have := hy.2
        show (1 : ℝ) - y ≠ 0
        linarith
      · subst hp1
        simp only [sub_self, zero_mul]
        exact continuousOn_const
    have c3 : ContinuousOn (fun y : ℝ => 2 * (p - y) ^ 2) (Set.Ioc 0 p) := by fun_prop
    exact (c1.neg.sub c2).sub c3
  have hanti : AntitoneOn G (Set.Ioc 0 p) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 p) hcont
      (f' := fun x => -p / x + (1 - p) / (1 - x) + 4 * (p - x)) ?_ ?_
    · intro x hx
      rw [interior_Ioc] at hx
      exact (hasDerivAt_pinskerAux p hx.1 (hx.2.trans_le hp)).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      have hx0 : 0 < x := hx.1
      have hx1 : 0 < 1 - x := by linarith [hx.2]
      have key : -p / x + (1 - p) / (1 - x) + 4 * (p - x) =
          (x - p) * (2 * x - 1) ^ 2 / (x * (1 - x)) := by
        field_simp
        ring
      rw [key]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (sq_nonneg _)) (by positivity)
  have hGq : G p ≤ G q := hanti ⟨hq, hqp⟩ ⟨hp0, le_rfl⟩ hqp
  simp only [hG] at hGq
  have e1 : p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
    rw [Real.log_div hp0.ne' hq.ne']
    ring
  have e2 : (1 - p) * Real.log ((1 - p) / (1 - q)) =
      (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - q) := by
    rcases hp.lt_or_eq with hp1 | hp1
    · rw [Real.log_div (by linarith) (by linarith)]
      ring
    · subst hp1
      simp
  rw [e1, e2]
  nlinarith [hGq]

/-- The total variation distance is nonnegative. -/
theorem tvDist_nonneg {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) : 0 ≤ tvDist P Q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- `d_TV(P, Q) = P(A) - Q(A)` for `A = {x | Q(x) < P(x)}`. -/
theorem tvDist_eq_measureReal_sub {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) :
    tvDist P Q =
      (P : Measure α).real
          (Finset.univ.filter fun x => (Q : Measure α).real {x} < (P : Measure α).real {x}) -
        (Q : Measure α).real
          (Finset.univ.filter fun x => (Q : Measure α).real {x} < (P : Measure α).real {x}) := by
  unfold tvDist
  simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [← sum_measureReal_singleton, ← sum_measureReal_singleton, Finset.sum_filter,
    Finset.sum_filter]
  have hμ : ∑ x, (P : Measure α).real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have hν : ∑ x, (Q : Measure α).real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have key : ∀ x, |(P : Measure α).real {x} - (Q : Measure α).real {x}| =
      2 * ((if (Q : Measure α).real {x} < (P : Measure α).real {x} then
            (P : Measure α).real {x} else 0) -
          (if (Q : Measure α).real {x} < (P : Measure α).real {x} then
            (Q : Measure α).real {x} else 0)) -
        ((P : Measure α).real {x} - (Q : Measure α).real {x}) := by
    intro x
    split_ifs with h
    · rw [abs_of_pos (by linarith)]
      ring
    · rw [abs_of_nonpos (by linarith)]
      ring
  rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, hμ, hν]
  ring

/-- **Pinsker's inequality** on a finite discrete space, with natural logarithm:
`2 d_TV(P, Q)² ≤ KL(P ‖ Q)` (`prop:decoupling`; [PW25, Theorem 7.10]). -/
theorem ofReal_two_mul_tvDist_sq_le_klDiv {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) :
    ENNReal.ofReal (2 * tvDist P Q ^ 2) ≤
      InformationTheory.klDiv (P : Measure α) (Q : Measure α) := by
  have htv := tvDist_eq_measureReal_sub P Q
  set μ : Measure α := (P : Measure α)
  set ν : Measure α := (Q : Measure α)
  set A : Finset α := Finset.univ.filter fun x => ν.real {x} < μ.real {x}
  let f : α → Bool := fun x => decide (ν.real {x} < μ.real {x})
  have hf : Measurable f := measurable_of_finite f
  have hAm : MeasurableSet (A : Set α) := A.measurableSet
  have hpreT : f ⁻¹' {true} = (A : Set α) := by
    ext x
    simp [f, A]
  have hpreF : f ⁻¹' {false} = (A : Set α)ᶜ := by
    ext x
    simp [f, A]
  have hqp : ν.real A ≤ μ.real A := by linarith [tvDist_nonneg P Q]
  rcases hqp.eq_or_lt with heq | hlt
  · have h0 : tvDist P Q = 0 := by rw [htv, heq, sub_self]
    simp [h0]
  rcases (measureReal_nonneg : 0 ≤ ν.real A).eq_or_lt with h0 | h0
  · have hnac : ¬ μ ≪ ν := by
      intro hac
      have hμ0 : μ A = 0 := hac ((measureReal_eq_zero_iff).1 h0.symm)
      have : μ.real A = 0 := (measureReal_eq_zero_iff).2 hμ0
      linarith
    rw [klDiv_of_not_ac hnac]
    exact le_top
  have hp1 : μ.real A ≤ 1 := measureReal_le_one
  have hne : ∀ b, (ν.map f) {b} ≠ 0 := by
    intro b hb
    have hb' : (ν.map f).real {b} = 0 := (measureReal_eq_zero_iff).2 hb
    rw [map_measureReal_apply hf (measurableSet_singleton b)] at hb'
    cases b
    · rw [hpreF, probReal_compl_eq_one_sub hAm] at hb'
      linarith
    · rw [hpreT] at hb'
      linarith
  refine le_trans ?_ (klDiv_map_le μ ν hf)
  rw [klDiv_eq_sum (μ.map f) (ν.map f) hne, Fintype.sum_bool]
  simp only [map_measureReal_apply hf (measurableSet_singleton _), hpreT, hpreF,
    probReal_compl_eq_one_sub hAm]
  apply ENNReal.ofReal_le_ofReal
  rw [htv]
  have := two_mul_sq_le_binaryKL h0 hqp hp1
  linarith

/-- **Pinsker's inequality**, square-root form:
`d_TV(P, Q) ≤ √(KL(P ‖ Q) / 2)` when `KL(P ‖ Q)` is finite. -/
theorem tvDist_le_sqrt_klDiv {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α)
    (h : InformationTheory.klDiv (P : Measure α) (Q : Measure α) ≠ ⊤) :
    tvDist P Q ≤ √((InformationTheory.klDiv (P : Measure α) (Q : Measure α)).toReal / 2) := by
  have h1 := ofReal_two_mul_tvDist_sq_le_klDiv P Q
  rw [ENNReal.ofReal_le_iff_le_toReal h] at h1
  apply Real.le_sqrt_of_sq_le
  linarith

end Parking

end
