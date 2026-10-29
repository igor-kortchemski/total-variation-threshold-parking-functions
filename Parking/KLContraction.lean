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

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Parking.CountPoly
public import Parking.Exchangeable
public import Parking.LogConcave
public import Parking.ProductMoments
import Parking.EntropyKL

/-!
# One-coordinate contraction of relative entropy

The complete log-concavity form of [LS26, Lemma 3.5]: for `m ≥ 1` and exchangeable laws
`μ, ν` on `[d]^m` whose count-generating polynomial `h_ν` is completely log-concave,
`D(μ_1 ‖ ν_1) ≤ (1 / m) D(μ ‖ ν)`, where `μ_1` and `ν_1` are the laws of the first
coordinate. It is a step towards the complete log-concavity form of [LS26, Lemma 3.7],
used in `lem:sample_entropy`.

* `sum_mul_sub_log_sum_exp_le_klDiv`: the finite Donsker–Varadhan (Gibbs) inequality
  `E_μ F - log E_ν e^F ≤ D(μ ‖ ν)` for probability laws `μ ≪ ν` on a finite set.
* `sum_mul_log_div_le_of_forall`: conversely, `D(μ ‖ ν)` is at most any upper bound of
  `E_μ η - log E_ν e^η` over all `η`. The test functions are `η = log (μ / ν)` where
  `μ > 0` and `η = log t` elsewhere, with `t > 0` arbitrarily small.
* `expectedCount_eq_mul_coordMarginalLaw`: for an exchangeable law `ν` on `[d]^m`, the
  expected number of occurrences of `a` is `m ν_1(a)`.
* `klDiv_coordMarginalLaw_le_of_completelyLogConcave`: the contraction. The proof follows
  [LS26, Lemma 3.5] without passing to count laws: the Donsker–Varadhan inequality on
  `[d]^m` with `F(ω) = ∑_j η_{ω_j}`, exchangeability of `μ`, and [LS26, inequality (3.6)]
  (`eval_countPoly_le_of_completelyLogConcave`) at `x = e^η` give
  `m (E_{μ_1} η - log E_{ν_1} e^η) ≤ D(μ ‖ ν)` for every `η`.

Everything here is unconditional.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace Parking

/-- If `μ ≪ ν` and `ν` is finite, a point charged by `μ` is charged by `ν`. -/
theorem measureReal_singleton_pos_of_ac {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsFiniteMeasure ν] (hac : μ ≪ ν) {x : α} (hx : 0 < μ.real {x}) : 0 < ν.real {x} := by
  refine lt_of_le_of_ne measureReal_nonneg fun h => ?_
  have hμ : μ {x} = 0 := hac ((measureReal_eq_zero_iff).1 h.symm)
  rw [measureReal_def, hμ, ENNReal.toReal_zero] at hx
  exact lt_irrefl _ hx

section Finite

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- For a probability law `ν` on a finite set and a positive function `f`,
`E_ν f = ∑ₓ ν(x) f(x) > 0`. -/
theorem sum_measureReal_mul_pos (ν : Measure α) [IsProbabilityMeasure ν] {f : α → ℝ}
    (hf : ∀ x, 0 < f x) : 0 < ∑ x, ν.real {x} * f x := by
  have h1 : ∑ x, ν.real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1.symm ▸ one_ne_zero)
  exact Finset.sum_pos' (fun y _ => mul_nonneg measureReal_nonneg (hf y).le)
    ⟨x, Finset.mem_univ x, mul_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm hx)) (hf x)⟩

/-- The finite Donsker–Varadhan (Gibbs) inequality, with the relative entropy written as a
sum: for probability laws `μ ≪ ν` on a finite set and any `F`,
`∑ₓ μ(x) F(x) - log ∑ₓ ν(x) e^{F(x)} ≤ ∑ₓ μ(x) log (μ(x) / ν(x))`. It sums the pointwise
inequalities `μ(x) u ≤ μ(x) (e^u - 1)` at `u = F(x) - log Z - log (μ(x) / ν(x))`, where
`Z = ∑ₓ ν(x) e^{F(x)}`. -/
theorem sum_mul_sub_log_sum_exp_le_sum (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) (F : α → ℝ) :
    ∑ x, μ.real {x} * F x - Real.log (∑ x, ν.real {x} * Real.exp (F x)) ≤
      ∑ x, μ.real {x} * Real.log (μ.real {x} / ν.real {x}) := by
  set Z := ∑ x, ν.real {x} * Real.exp (F x) with hZ
  have hZ0 : 0 < Z := sum_measureReal_mul_pos ν fun x => Real.exp_pos (F x)
  have hμ1 : ∑ x, μ.real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have hpt (x : α) : μ.real {x} * F x - μ.real {x} * Real.log Z -
      μ.real {x} * Real.log (μ.real {x} / ν.real {x}) ≤
      ν.real {x} * Real.exp (F x) / Z - μ.real {x} := by
    rcases (measureReal_nonneg (μ := μ) (s := {x})).eq_or_lt with h0 | hp
    · rw [← h0]
      simp only [zero_mul, sub_zero]
      exact div_nonneg (mul_nonneg measureReal_nonneg (Real.exp_pos _).le) hZ0.le
    · have hq := measureReal_singleton_pos_of_ac hac hp
      set u := F x - Real.log Z - Real.log (μ.real {x} / ν.real {x}) with hu
      have hexp : μ.real {x} * Real.exp u = ν.real {x} * Real.exp (F x) / Z := by
        rw [hu, Real.exp_sub, Real.exp_sub, Real.exp_log hZ0, Real.exp_log (div_pos hp hq)]
        field_simp
      have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp u) hp.le
      rw [mul_add, mul_one, hexp, hu] at h
      linarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpt x
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hμ1, ← Finset.sum_div, ← hZ, div_self hZ0.ne'] at hsum
  linarith

/-- The finite Donsker–Varadhan (Gibbs) inequality: for probability laws `μ ≪ ν` on a
finite set with measurable singletons and any `F`,
`∑ₓ μ(x) F(x) - log ∑ₓ ν(x) e^{F(x)} ≤ D(μ ‖ ν)`, with `D(μ ‖ ν)` Mathlib's `klDiv`
(finite under `μ ≪ ν`). -/
theorem sum_mul_sub_log_sum_exp_le_klDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) (F : α → ℝ) :
    ∑ x, μ.real {x} * F x - Real.log (∑ x, ν.real {x} * Real.exp (F x)) ≤
      (klDiv μ ν).toReal := by
  rw [klDiv_eq_sum_of_ac μ ν hac, ENNReal.toReal_ofReal']
  exact (sum_mul_sub_log_sum_exp_le_sum μ ν hac F).trans (le_max_left _ _)

/-- The relative entropy is the supremum in the Donsker–Varadhan formula: for probability
laws `μ ≪ ν` on a finite set, if `∑ₓ μ(x) η(x) - log ∑ₓ ν(x) e^{η(x)} ≤ C` for every `η`,
then `∑ₓ μ(x) log (μ(x) / ν(x)) ≤ C`. Take `η = log (μ / ν)` where `μ > 0` and
`η = log t` elsewhere: the first sum is the relative entropy and the second is at most
`1 + t`, so the relative entropy is at most `C + t` for every `t > 0`. -/
theorem sum_mul_log_div_le_of_forall {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) {C : ℝ}
    (hC : ∀ η : α → ℝ,
      ∑ x, μ.real {x} * η x - Real.log (∑ x, ν.real {x} * Real.exp (η x)) ≤ C) :
    ∑ x, μ.real {x} * Real.log (μ.real {x} / ν.real {x}) ≤ C := by
  classical
  have hμ1 : ∑ x, μ.real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  have hν1 : ∑ x, ν.real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  refine le_of_forall_pos_le_add fun t ht => ?_
  let η : α → ℝ := fun x =>
    if μ.real {x} = 0 then Real.log t else Real.log (μ.real {x} / ν.real {x})
  have h1 : ∑ x, μ.real {x} * η x = ∑ x, μ.real {x} * Real.log (μ.real {x} / ν.real {x}) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : μ.real {x} = 0
    · rw [hx, zero_mul, zero_mul]
    · simp only [η, hx, ↓reduceIte]
  have hle (x : α) : ν.real {x} * Real.exp (η x) ≤ μ.real {x} + ν.real {x} * t := by
    by_cases hx : μ.real {x} = 0
    · simp only [η, hx, ↓reduceIte, Real.exp_log ht, zero_add, le_refl]
    · have hp : 0 < μ.real {x} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hx)
      have hq := measureReal_singleton_pos_of_ac hac hp
      simp only [η, hx, ↓reduceIte, Real.exp_log (div_pos hp hq)]
      rw [mul_div_cancel₀ _ hq.ne']
      linarith [mul_nonneg hq.le ht.le]
  have h2 : ∑ x, ν.real {x} * Real.exp (η x) ≤ 1 + t :=
    calc _ ≤ ∑ x, (μ.real {x} + ν.real {x} * t) := Finset.sum_le_sum fun x _ => hle x
      _ = 1 + t := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hμ1, hν1, one_mul]
  have hpos : 0 < ∑ x, ν.real {x} * Real.exp (η x) :=
    sum_measureReal_mul_pos ν fun _ => Real.exp_pos _
  have h3 : Real.log (∑ x, ν.real {x} * Real.exp (η x)) ≤ t :=
    calc _ ≤ Real.log (1 + t) := Real.log_le_log hpos h2
      _ ≤ 1 + t - 1 := Real.log_le_sub_one_of_pos (by linarith)
      _ = t := by ring
  have h4 := hC η
  rw [h1] at h4
  linarith

end Finite

/-! ### Exchangeable laws on words -/

/-- For an exchangeable law `ν` on `[d]^m` with `m > 0`, the expected number of occurrences
of the letter `a` is `m ν_1(a)`, where `ν_1` is the law of the first coordinate
([LS26, proof of Lemma 3.5]): every coordinate has law `ν_1`. -/
theorem expectedCount_eq_mul_coordMarginalLaw {m d : ℕ} (hm : 0 < m)
    (ν : Measure (Fin m → Fin d)) [IsFiniteMeasure ν] (hν : IsExchangeableLaw ν) (a : Fin d) :
    expectedCount ν a = m * (coordMarginalLaw ν ⟨0, hm⟩).real {a} := by
  have h1 : expectedCount ν a = ∑ ω, ν.real {ω} * ∑ j, (if ω j = a then (1 : ℝ) else 0) := by
    rw [← sum_expectedCount_mul ν fun b => if b = a then (1 : ℝ) else 0]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have h2 (j : Fin m) : ∑ ω, ν.real {ω} * (if ω j = a then (1 : ℝ) else 0) =
      (coordMarginalLaw ν ⟨0, hm⟩).real {a} := by
    have h := sum_measureReal_mul_apply ν j fun b => if b = a then (1 : ℝ) else 0
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at h ⊢
    rw [h, ← hν.coordMarginalLaw_eq j ⟨0, hm⟩]
    rfl
  rw [h1]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- The variational lower bound in the proof of [LS26, Lemma 3.5], under complete
log-concavity of `h_ν`: for exchangeable probability laws `μ ≪ ν` on `[d]^m` with `m ≥ 1`
and any `η`, `m (∑_a μ_1(a) η_a - log ∑_a ν_1(a) e^{η_a}) ≤ ∑_ω μ(ω) log (μ(ω) / ν(ω))`.
This is the Donsker–Varadhan inequality for `F(ω) = ∑_j η_{ω_j}`: exchangeability of `μ`
gives `E_μ F = m ∑_a μ_1(a) η_a`, and `E_ν e^F = h_ν(e^η) ≤ (∑_a ν_1(a) e^{η_a})^m` by
[LS26, inequality (3.6)] and exchangeability of `ν`. -/
theorem mul_sub_log_le_of_completelyLogConcave {m d : ℕ} (hm : 1 ≤ m)
    (μ ν : Measure (Fin m → Fin d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsExchangeableLaw μ) (hν : IsExchangeableLaw ν)
    (h : CompletelyLogConcave (countPoly ν)) (hac : μ ≪ ν) (η : Fin d → ℝ) :
    (m : ℝ) * (∑ a, (coordMarginalLaw μ ⟨0, hm⟩).real {a} * η a -
      Real.log (∑ a, (coordMarginalLaw ν ⟨0, hm⟩).real {a} * Real.exp (η a))) ≤
      ∑ ω, μ.real {ω} * Real.log (μ.real {ω} / ν.real {ω}) := by
  have hDV := sum_mul_sub_log_sum_exp_le_sum μ ν hac fun ω => ∑ j, η (ω j)
  have h1 : ∑ ω, μ.real {ω} * ∑ j, η (ω j) =
      m * ∑ a, (coordMarginalLaw μ ⟨0, hm⟩).real {a} * η a := by
    rw [← sum_expectedCount_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [expectedCount_eq_mul_coordMarginalLaw hm μ hμ a, mul_assoc]
  have h2 : ∑ ω, ν.real {ω} * Real.exp (∑ j, η (ω j)) =
      MvPolynomial.eval (fun a => Real.exp (η a)) (countPoly ν) := by
    rw [eval_countPoly]
    simp only [Real.exp_sum]
  have h3 := eval_countPoly_le_of_completelyLogConcave hm ν h (fun a => Real.exp (η a))
    fun a => Real.exp_pos _
  have h4 : (1 / (m : ℝ)) * ∑ a, expectedCount ν a * Real.exp (η a) =
      ∑ a, (coordMarginalLaw ν ⟨0, hm⟩).real {a} * Real.exp (η a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [expectedCount_eq_mul_coordMarginalLaw hm ν hν a]
    field_simp
  rw [h4, ← h2] at h3
  have hpos : 0 < ∑ ω, ν.real {ω} * Real.exp (∑ j, η (ω j)) :=
    sum_measureReal_mul_pos ν fun _ => Real.exp_pos _
  have h5 := Real.log_le_log hpos h3
  rw [Real.log_pow] at h5
  rw [h1] at hDV
  rw [mul_sub]
  linarith

/-! ### The contraction -/

/-- The complete log-concavity form of [LS26, Lemma 3.5]: for `m ≥ 1` and exchangeable
probability laws `μ, ν` on `[d]^m` such that the count-generating polynomial `h_ν` is
completely log-concave, the laws `μ_1, ν_1` of the first coordinate satisfy
`D(μ_1 ‖ ν_1) ≤ (1 / m) D(μ ‖ ν)`. If `μ` is not absolutely continuous with respect to `ν`,
the right side is infinite. Otherwise `μ_1 ≪ ν_1`, and the bound follows from
`mul_sub_log_le_of_completelyLogConcave` and `sum_mul_log_div_le_of_forall`. -/
theorem klDiv_coordMarginalLaw_le_of_completelyLogConcave {m d : ℕ} (hm : 1 ≤ m)
    (μ ν : Measure (Fin m → Fin d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsExchangeableLaw μ) (hν : IsExchangeableLaw ν)
    (h : CompletelyLogConcave (countPoly ν)) :
    InformationTheory.klDiv (coordMarginalLaw μ ⟨0, hm⟩) (coordMarginalLaw ν ⟨0, hm⟩) ≤
      ((m : ℝ≥0∞))⁻¹ * InformationTheory.klDiv μ ν := by
  by_cases hac : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hac, ENNReal.mul_top (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))]
    exact le_top
  have : IsProbabilityMeasure (coordMarginalLaw μ ⟨0, hm⟩) := by
    unfold coordMarginalLaw; infer_instance
  have : IsProbabilityMeasure (coordMarginalLaw ν ⟨0, hm⟩) := by
    unfold coordMarginalLaw; infer_instance
  have hac1 : coordMarginalLaw μ ⟨0, hm⟩ ≪ coordMarginalLaw ν ⟨0, hm⟩ :=
    hac.map (measurable_of_finite _)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have key := sum_mul_log_div_le_of_forall hac1
    (C := (m : ℝ)⁻¹ * ∑ ω, μ.real {ω} * Real.log (μ.real {ω} / ν.real {ω})) fun η => by
      rw [le_inv_mul_iff₀ hm0]
      exact mul_sub_log_le_of_completelyLogConcave hm μ ν hμ hν h hac η
  rw [klDiv_eq_sum_of_ac _ _ hac1, klDiv_eq_sum_of_ac μ ν hac]
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal ((m : ℝ)⁻¹ *
        ∑ ω, μ.real {ω} * Real.log (μ.real {ω} / ν.real {ω})) := ENNReal.ofReal_le_ofReal key
    _ = _ := by
      rw [ENNReal.ofReal_mul (inv_nonneg.2 hm0.le), ENNReal.ofReal_inv_of_pos hm0,
        ENNReal.ofReal_natCast]

end Parking

end
