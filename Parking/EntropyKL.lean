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

public import Parking.Entropy
public import Parking.Law
public import Parking.Exchangeable
import Parking.WordLaw
import Parking.Count

/-!
# Entropy and relative entropy of laws on a finite set

Elementary facts used in the proofs of `lem:sample_entropy` and `prop:decoupling`.

* `entropy_nonneg`, `entropy_le_log_card`, `entropy_map_of_injective`, `entropy_map_equiv`,
  `entropy_uniformLaw`: basic properties of the Shannon entropy `H` (natural logarithm).
* `klDiv_eq_sum_of_ac`: for probability laws `μ ≪ ν` on a finite set,
  `KL(μ ‖ ν) = ∑ₓ μ(x) log (μ(x) / ν(x))`, without assuming that `ν` charges every point.
* `klDiv_pi_eq_entropy` (Entropy-defect identity, `lem:sample_entropy`): if every coordinate of a
  law `L` on `[d]^m` has law `μ`, then `KL(L ‖ μ^{⊗m}) = m H(μ) - H(L)`.
* `klDiv_firstCoordsLaw_self_le` (Full-vector KL bound, `prop:decoupling`):
  `KL(P_{n,n} ‖ μ_n^{⊗n}) ≤ log n`. Indeed `P_{n,n}` is uniform on the `(n + 1)^{n - 1}`
  parking functions. The proof now consumes the displayed identity
  `KL(P_{n,n} ‖ μ_n^{⊗n}) = log(n^n/(n+1)^{n-1}) - n KL(μ_n ‖ U_n)`
  and nonnegativity of the marginal divergence. Both real and ENNReal versions of
  that identity are exposed below.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory

namespace Parking

section Finite

variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Entropy -/

/-- The entropy of a probability law on a finite set is nonnegative. -/
theorem entropy_nonneg (μ : Measure α) [IsProbabilityMeasure μ] : 0 ≤ entropy μ :=
  Finset.sum_nonneg fun _ _ => Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

/-- Pointwise form of Gibbs' inequality: `-p log p ≤ p log N + (1 / N - p)` for `p ≥ 0` and
`N > 0`, from `log t ≤ t - 1` at `t = 1 / (N p)`. -/
theorem negMulLog_le_mul_log_add {p N : ℝ} (hp : 0 ≤ p) (hN : 0 < N) :
    Real.negMulLog p ≤ p * Real.log N + (N⁻¹ - p) := by
  rcases hp.eq_or_lt with rfl | hp
  · simp only [Real.negMulLog_zero, zero_mul, sub_zero, zero_add, inv_nonneg, hN.le]
  · have h := Real.log_le_sub_one_of_pos (inv_pos.2 (mul_pos hN hp))
    rw [Real.log_inv, Real.log_mul hN.ne' hp.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h hp.le
    have e : p * ((N * p)⁻¹ - 1) = N⁻¹ - p := by
      field_simp
    rw [e] at h'
    rw [Real.negMulLog]
    linarith

/-- The entropy of a probability law on a finite set `α` is at most `log |α|`. -/
theorem entropy_le_log_card (μ : Measure α) [IsProbabilityMeasure μ] :
    entropy μ ≤ Real.log (Fintype.card α) := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ x, μ.real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  calc entropy μ
      ≤ ∑ x, (μ.real {x} * Real.log (Fintype.card α) +
          ((Fintype.card α : ℝ)⁻¹ - μ.real {x})) :=
        Finset.sum_le_sum fun x _ => negMulLog_le_mul_log_add measureReal_nonneg hN
    _ = Real.log (Fintype.card α) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, Finset.sum_sub_distrib, hsum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hN.ne']
        ring

variable [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Entropy is invariant under an injective relabelling of the points. -/
theorem entropy_map_of_injective (μ : Measure α) {f : α → β} (hf : Function.Injective f) :
    entropy (μ.map f) = entropy μ := by
  simp only [entropy]
  refine (Fintype.sum_of_injective f hf _ _ (fun y hy => ?_) (fun x => ?_)).symm
  · have h : f ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hy ⟨x, hx⟩
    rw [map_measureReal_apply (measurable_of_finite f) (measurableSet_singleton y), h,
      measureReal_empty, Real.negMulLog_zero]
  · have h : f ⁻¹' {f x} = {x} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hf.eq_iff]
    rw [map_measureReal_apply (measurable_of_finite f) (measurableSet_singleton _), h]

/-- Entropy is invariant under a bijection between finite sets. -/
theorem entropy_map_equiv (μ : Measure α) (e : α ≃ β) : entropy (μ.map e) = entropy μ :=
  entropy_map_of_injective μ e.injective

/-- The entropy of the uniform law on a finite nonempty set `α` is `log |α|`. -/
theorem entropy_uniformLaw [Nonempty α] :
    entropy (uniformLaw α : Measure α) = Real.log (Fintype.card α) := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h (x : α) : (uniformLaw α : Measure α).real {x} = (Fintype.card α : ℝ)⁻¹ := by
    have hx := uniformLaw_apply (α := α) {x}
    rw [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one, one_div] at hx
    rw [ProbabilityMeasure.measureReal_eq_coe_coeFn, hx]
  simp only [entropy, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog,
    Real.log_inv]
  field_simp

/-! ### Relative entropy -/

omit [MeasurableSingletonClass α] in
/-- On a finite set, `μ ≪ ν` as soon as every atom that is `ν`-null is `μ`-null. -/
theorem absolutelyContinuous_of_forall_singleton {μ ν : Measure α}
    (h : ∀ x, ν {x} = 0 → μ {x} = 0) : μ ≪ ν := by
  intro s hs
  rw [← Set.biUnion_of_singleton s, measure_biUnion_null_iff s.to_countable]
  exact fun x hx => h x (measure_mono_null (Set.singleton_subset_iff.2 hx) hs)

/-- On a finite discrete space, for probability laws `μ ≪ ν`, Mathlib's `klDiv` is the
source formula `∑ₓ μ(x) log (μ(x) / ν(x))` (`prop:decoupling`), the terms with `μ(x) = 0` being
zero. Unlike `klDiv_eq_sum`, `ν` need not charge every point. -/
theorem klDiv_eq_sum_of_ac (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) :
    klDiv μ ν = ENNReal.ofReal (∑ x, μ.real {x} * Real.log (μ.real {x} / ν.real {x})) := by
  rw [klDiv_of_ac_of_integrable hac Integrable.of_finite]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_fintype Integrable.of_finite]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_eq_mul, llr]
  by_cases hμx : μ {x} = 0
  · have h0 : μ.real {x} = 0 := by simp only [measureReal_def, hμx, ENNReal.toReal_zero]
    rw [h0, zero_mul, zero_mul]
  · have hνx : ν {x} ≠ 0 := fun h => hμx (hac h)
    congr 2
    have h := Measure.setLIntegral_rnDeriv hac {x}
    rw [lintegral_singleton] at h
    have hr : μ.rnDeriv ν x = μ {x} / ν {x} :=
      (ENNReal.eq_div_iff hνx (measure_ne_top _ _)).mpr (by rw [mul_comm]; exact h)
    rw [hr, ENNReal.toReal_div]
    rfl

/-- The real-valued finite divergence formula; nonnegativity is supplied by Mathlib. -/
theorem toReal_klDiv_eq_sum_finite (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ x, μ.real {x} * Real.log (μ.real {x} / ν.real {x}) := by
  rw [toReal_klDiv hac Integrable.of_finite]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_eq_mul, llr]
  by_cases hμx : μ {x} = 0
  · have h0 : μ.real {x} = 0 := by simp only [measureReal_def, hμx, ENNReal.toReal_zero]
    rw [h0, zero_mul, zero_mul]
  · have hνx : ν {x} ≠ 0 := fun h => hμx (hac h)
    congr 2
    have h := Measure.setLIntegral_rnDeriv hac {x}
    rw [lintegral_singleton] at h
    have hr : μ.rnDeriv ν x = μ {x} / ν {x} :=
      (ENNReal.eq_div_iff hνx (measure_ne_top _ _)).mpr (by rw [mul_comm]; exact h)
    rw [hr, ENNReal.toReal_div]
    rfl

/-- Relative entropy with respect to the uniform law is the entropy deficit.
This identity includes laws having zero atoms. -/
theorem klDiv_uniformLaw_eq [Nonempty α] (μ : Measure α) [IsProbabilityMeasure μ] :
    klDiv μ (uniformLaw α : Measure α) =
      ENNReal.ofReal (Real.log (Fintype.card α) - entropy μ) := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hu (x : α) : (uniformLaw α : Measure α).real {x} =
      (Fintype.card α : ℝ)⁻¹ := by
    have hx := uniformLaw_apply (α := α) {x}
    rw [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one, one_div] at hx
    rw [ProbabilityMeasure.measureReal_eq_coe_coeFn, hx]
  have hune (x : α) : (uniformLaw α : Measure α) {x} ≠ 0 := by
    intro hx
    have he := hu x
    rw [measureReal_def, hx, ENNReal.toReal_zero] at he
    exact (inv_pos.mpr hN).ne' he.symm
  rw [klDiv_eq_sum μ _ hune]
  congr 1
  have hterm (x : α) :
      μ.real {x} * Real.log (μ.real {x} / (uniformLaw α : Measure α).real {x}) =
        -Real.negMulLog (μ.real {x}) + μ.real {x} * Real.log (Fintype.card α) := by
    rcases (measureReal_nonneg (μ := μ) (s := {x})).eq_or_lt with hp | hp
    · simp [← hp]
    · rw [hu, Real.log_div hp.ne' (inv_ne_zero hN.ne'), Real.log_inv, Real.negMulLog]
      ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul,
    sum_measureReal_singleton, Finset.coe_univ, probReal_univ, one_mul]
  change -entropy μ + Real.log (Fintype.card α) = _
  ring

/-- The real form of the uniform entropy-deficit identity. -/
theorem toReal_klDiv_uniformLaw_eq [Nonempty α] (μ : Measure α) [IsProbabilityMeasure μ] :
    (klDiv μ (uniformLaw α : Measure α)).toReal =
      Real.log (Fintype.card α) - entropy μ := by
  rw [klDiv_uniformLaw_eq, ENNReal.toReal_ofReal (sub_nonneg.mpr (entropy_le_log_card μ))]

end Finite

/-! ### Relative entropy with respect to the product of the marginals -/

/-- The mass of a point under a product law is the product of the masses of its
coordinates. -/
theorem measureReal_pi_singleton {ι γ : Type*} [Fintype ι] [MeasurableSpace γ]
    (μ : Measure γ) [SigmaFinite μ] (x : ι → γ) :
    (Measure.pi fun _ : ι => μ).real {x} = ∏ i, μ.real {x i} := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

/-- Integrating a function of coordinate `i` against a law on `[d]^m` amounts to
integrating it against the law of that coordinate. -/
theorem sum_measureReal_mul_apply {m d : ℕ} (L : Measure (Fin m → Fin d)) [IsFiniteMeasure L]
    (i : Fin m) (g : Fin d → ℝ) :
    ∑ x, L.real {x} * g (x i) = ∑ a, (L.map fun x => x i).real {a} * g a := by
  have h1 := integral_fintype (μ := L) (f := fun x => g (x i)) Integrable.of_finite
  have h2 := integral_fintype (μ := L.map fun x => x i) (f := g) Integrable.of_finite
  have h3 : ∫ a, g a ∂(L.map fun x => x i) = ∫ x, g (x i) ∂L :=
    integral_map (measurable_of_finite _).aemeasurable
      (measurable_of_finite g).aestronglyMeasurable
  simp only [smul_eq_mul] at h1 h2
  rw [← h1, ← h2, h3]

/-- If coordinate `i` of a finite law `L` on `[d]^m` has law `μ`, then
`L({x}) ≤ μ({x_i})`. -/
theorem measureReal_singleton_le_of_coordMarginalLaw {m d : ℕ} (L : Measure (Fin m → Fin d))
    [IsFiniteMeasure L] {μ : Measure (Fin d)} {i : Fin m} (hL : coordMarginalLaw L i = μ)
    (x : Fin m → Fin d) : L.real {x} ≤ μ.real {x i} := by
  rw [← hL, coordMarginalLaw,
    map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _)]
  exact measureReal_mono fun y hy => by
    simp only [Set.mem_singleton_iff.1 hy, Set.mem_preimage, Set.mem_singleton_iff]

/-- A law on `[d]^m` whose coordinates all have law `μ` is absolutely continuous with
respect to `μ^{⊗m}`: if `L({x}) > 0`, then `μ({x_i}) ≥ L({x}) > 0` for every `i`. -/
theorem absolutelyContinuous_pi_of_coordMarginalLaw {m d : ℕ} (L : Measure (Fin m → Fin d))
    (μ : Measure (Fin d)) [IsProbabilityMeasure μ] (hL : ∀ i, coordMarginalLaw L i = μ) :
    L ≪ Measure.pi fun _ : Fin m => μ := by
  refine absolutelyContinuous_of_forall_singleton fun x hx => ?_
  rw [Measure.pi_singleton, Finset.prod_eq_zero_iff] at hx
  obtain ⟨i, -, hi⟩ := hx
  rw [← hL i, coordMarginalLaw,
    Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)] at hi
  exact measure_mono_null (fun y hy => by
    simp only [Set.mem_singleton_iff.1 hy, Set.mem_preimage, Set.mem_singleton_iff]) hi

/-- Node Entropy-defect identity (`lem:sample_entropy`): if every coordinate of a
law `L` on `[d]^m` has law `μ`, then `KL(L ‖ μ^{⊗m}) = m H(μ) - H(L)`. -/
theorem sum_klDiv_pi_eq_entropy {m d : ℕ} (L : Measure (Fin m → Fin d)) [IsProbabilityMeasure L]
    (μ : Measure (Fin d)) [IsProbabilityMeasure μ] (hL : ∀ i, coordMarginalLaw L i = μ) :
    (∑ x, L.real {x} * Real.log (L.real {x} / (Measure.pi fun _ : Fin m => μ).real {x})) =
      m * entropy μ - entropy L := by
  have hterm (x : Fin m → Fin d) :
      L.real {x} * Real.log (L.real {x} / (Measure.pi fun _ : Fin m => μ).real {x}) =
        -Real.negMulLog (L.real {x}) - ∑ i, L.real {x} * Real.log (μ.real {x i}) := by
    rw [measureReal_pi_singleton]
    rcases (measureReal_nonneg (μ := L) (s := {x})).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [zero_div, Real.log_zero, mul_zero, Real.negMulLog_zero, neg_zero, zero_mul,
        Finset.sum_const_zero, sub_self]
    · have hμpos (i : Fin m) : 0 < μ.real {x i} :=
        hpos.trans_le (measureReal_singleton_le_of_coordMarginalLaw L (hL i) x)
      rw [Real.log_div hpos.ne' (Finset.prod_pos fun i _ => hμpos i).ne',
        Real.log_prod fun i _ => (hμpos i).ne', Real.negMulLog, ← Finset.mul_sum]
      ring
  have hcoord (i : Fin m) : ∑ x, L.real {x} * Real.log (μ.real {x i}) = -entropy μ := by
    rw [sum_measureReal_mul_apply L i fun a => Real.log (μ.real {a}),
      show (L.map fun x => x i) = μ from hL i, entropy, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Real.negMulLog]
    ring
  calc ∑ x, L.real {x} * Real.log (L.real {x} / (Measure.pi fun _ : Fin m => μ).real {x})
      = ∑ x, -Real.negMulLog (L.real {x}) -
          ∑ x, ∑ i, L.real {x} * Real.log (μ.real {x i}) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => hterm x
    _ = -entropy L - ∑ i, ∑ x, L.real {x} * Real.log (μ.real {x i}) := by
        rw [Finset.sum_neg_distrib, Finset.sum_comm]
        rfl
    _ = m * entropy μ - entropy L := by
        rw [Finset.sum_congr rfl fun i _ => hcoord i, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The ENNReal entropy-defect identity. -/
theorem klDiv_pi_eq_entropy {m d : ℕ} (L : Measure (Fin m → Fin d)) [IsProbabilityMeasure L]
    (μ : Measure (Fin d)) [IsProbabilityMeasure μ] (hL : ∀ i, coordMarginalLaw L i = μ) :
    InformationTheory.klDiv L (Measure.pi fun _ : Fin m => μ) =
      ENNReal.ofReal (m * entropy μ - entropy L) := by
  rw [klDiv_eq_sum_of_ac L _ (absolutelyContinuous_pi_of_coordMarginalLaw L μ hL),
    sum_klDiv_pi_eq_entropy L μ hL]

/-- The real-valued entropy-defect identity. -/
theorem toReal_klDiv_pi_eq_entropy {m d : ℕ} (L : Measure (Fin m → Fin d)) [IsProbabilityMeasure L]
    (μ : Measure (Fin d)) [IsProbabilityMeasure μ] (hL : ∀ i, coordMarginalLaw L i = μ) :
    (InformationTheory.klDiv L (Measure.pi fun _ : Fin m => μ)).toReal =
      m * entropy μ - entropy L := by
  rw [toReal_klDiv_eq_sum_finite L _ (absolutelyContinuous_pi_of_coordMarginalLaw L μ hL),
    sum_klDiv_pi_eq_entropy L μ hL]

/-! ### The full relative entropy bound of `prop:decoupling` -/

/-- Keeping all `n` coordinates of a parking function is injective. -/
theorem firstCoords_self_injective (n : ℕ+) : Function.Injective (firstCoords n n le_rfl) :=
  fun _ _ h => Subtype.ext (funext fun r => congrFun h r)

/-- `H(P_{n,n}) = (n - 1) log (n + 1)`: `P_{n,n}` is uniform on the `(n + 1)^{n - 1}`
parking functions. -/
theorem entropy_firstCoordsLaw_self (n : ℕ+) :
    entropy (firstCoordsLaw n n le_rfl : Measure (Fin n → Fin n)) =
      ((n : ℕ) - 1 : ℕ) * Real.log ((n : ℕ) + 1) := by
  rw [firstCoordsLaw, ProbabilityMeasure.toMeasure_map,
    entropy_map_of_injective _ (firstCoords_self_injective n), uniformParking,
    entropy_uniformLaw, card_parkingFunction, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

/-- Every coordinate of `P_{n,n}` has law `μ_n`. -/
theorem coordMarginalLaw_firstCoordsLaw_self (n : ℕ+) (i : Fin n) :
    coordMarginalLaw (firstCoordsLaw n n le_rfl : Measure (Fin n → Fin n)) i = marginal n := by
  rw [marginal_eq_coordMarginalLaw n i, firstCoordsLaw_eq_coordLaw]
  congr 1
  exact Measure.map_id

/-- The displayed full-vector KL identity in `prop:decoupling`.
The marginal KL is real-valued because the uniform law has full support. -/
theorem klDiv_firstCoordsLaw_self_eq (n : ℕ+) :
    InformationTheory.klDiv (firstCoordsLaw n n le_rfl : Measure (Fin n → Fin n))
        (marginalProduct n n : Measure (Fin n → Fin n)) =
      ENNReal.ofReal (Real.log ((n : ℝ) ^ (n : ℕ) / ((n : ℝ) + 1) ^ ((n : ℕ) - 1)) -
        (n : ℝ) * (InformationTheory.klDiv (marginal n : Measure (Fin n))
          (uniformLaw (Fin n) : Measure (Fin n))).toReal) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hprod : (marginalProduct n n : Measure (Fin n → Fin n)) =
      Measure.pi fun _ : Fin n => (marginal n : Measure (Fin n)) :=
    ProbabilityMeasure.toMeasure_pi _
  rw [hprod, klDiv_pi_eq_entropy _ _ (coordMarginalLaw_firstCoordsLaw_self n),
    entropy_firstCoordsLaw_self, toReal_klDiv_uniformLaw_eq, Fintype.card_fin,
    Real.log_div (pow_ne_zero _ hn.ne') (pow_ne_zero _ hnp.ne'), Real.log_pow, Real.log_pow]
  congr 1
  ring

/-- The manuscript full-vector identity as an equality of finite real divergences. -/
theorem toReal_klDiv_firstCoordsLaw_self_eq (n : ℕ+) :
    (InformationTheory.klDiv (firstCoordsLaw n n le_rfl : Measure (Fin n → Fin n))
        (marginalProduct n n : Measure (Fin n → Fin n))).toReal =
      Real.log ((n : ℝ) ^ (n : ℕ) / ((n : ℝ) + 1) ^ ((n : ℕ) - 1)) -
        (n : ℝ) * (InformationTheory.klDiv (marginal n : Measure (Fin n))
          (uniformLaw (Fin n) : Measure (Fin n))).toReal := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hprod : (marginalProduct n n : Measure (Fin n → Fin n)) =
      Measure.pi fun _ : Fin n => (marginal n : Measure (Fin n)) :=
    ProbabilityMeasure.toMeasure_pi _
  rw [hprod, toReal_klDiv_pi_eq_entropy _ _ (coordMarginalLaw_firstCoordsLaw_self n),
    entropy_firstCoordsLaw_self, toReal_klDiv_uniformLaw_eq, Fintype.card_fin,
    Real.log_div (pow_ne_zero _ hn.ne') (pow_ne_zero _ hnp.ne'), Real.log_pow, Real.log_pow]
  ring

/-- Node Full-vector KL bound, obtained by discarding the nonnegative
marginal divergence in the manuscript's displayed identity. -/
theorem klDiv_firstCoordsLaw_self_le (n : ℕ+) :
    InformationTheory.klDiv (firstCoordsLaw n n le_rfl : Measure (Fin n → Fin n))
        (marginalProduct n n : Measure (Fin n → Fin n)) ≤ ENNReal.ofReal (Real.log n) := by
  rw [klDiv_firstCoordsLaw_self_eq]
  apply ENNReal.ofReal_le_ofReal
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hlog : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hKL : 0 ≤ (n : ℝ) * (InformationTheory.klDiv (marginal n : Measure (Fin n))
      (uniformLaw (Fin n) : Measure (Fin n))).toReal :=
    mul_nonneg (by linarith) ENNReal.toReal_nonneg
  rw [Real.log_div (pow_ne_zero _ (by linarith : (n : ℝ) ≠ 0))
    (pow_ne_zero _ hnp.ne'), Real.log_pow, Real.log_pow, Nat.cast_sub n.pos, Nat.cast_one]
  have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ (n : ℝ) - 1)
  nlinarith

end Parking

end
