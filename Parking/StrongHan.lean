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
public import Mathlib.Probability.ConditionalProbability
public import Parking.CountPoly
public import Parking.Paper.Lorentzian
public import Parking.Entropy
public import Parking.Exchangeable
public import Parking.LogConcave
import Parking.EntropyKL
import Parking.KLContraction
import Parking.PrefixLaw

/-!
# The strengthened Han inequality for laws with completely log-concave count polynomial

`lem:sample_entropy`, applies [LS26, Lemma 3.7] (the strengthened Han
inequality for exchangeable Lorentzian laws) to the initial segments of the uniform parking
function. This file proves its analogue for exchangeable laws whose count-generating
polynomial is completely log-concave, without external input, following the proof of
[LS26, Lemma 3.7]: induction on the number of coordinates, conditioning on the last one.

* `entropy_map_prod_eq`, `entropy_eq_add_sum_cond`: the chain rule
  `H(Y, Z) = H(Z) + ∑_z P(Z = z) H(Y | Z = z)` for random variables on a finite probability
  space, the conditional laws being given by `ProbabilityTheory.cond`. In other words, the
  conditional entropy `H(Y | Z) = H(Y, Z) - H(Z)` is the average of the entropies of the
  conditional laws ([LS26, §3.1]).
* `sum_mul_toReal_klDiv_cond`: [LS26, Proposition 3.2],
  `∑_z P(Z = z) D(L(Y | Z = z) ‖ L(Y)) = H(Y) + H(Z) - H(Y, Z) = I(Y; Z)`.
* `condLastLaw`: the law `L(X_{[m]} | X_{m+1} = a)` of the first `m` coordinates of a random
  word `X` of length `m + 1`, conditionally on its last letter being `a`.
* `IsExchangeableLaw.condLastLaw`, `countPoly_condLastLaw`,
  `completelyLogConcave_countPoly_condLastLaw`: the complete log-concavity form of
  [LS26, Lemma 3.4(2)]. For an exchangeable law `μ` on `[d]^{m+1}` such that
  `P(X_{m+1} = a) > 0`, the conditional law is exchangeable, with count-generating
  polynomial `∂_a h_μ / ((m + 1) P(X_{m+1} = a))`, hence completely log-concave when `h_μ` is.
* `strongHan_of_completelyLogConcave`: the complete log-concavity analogue of
  [LS26, Lemma 3.7], `∑_j H(X_{[m] ∖ j}) ≥ (m - 2) H(X) + ∑_j H(X_j)` for `m ≥ 2`.
* `mul_entropy_coordLaw_ge_of_completelyLogConcave`: the form used in
  `lem:sample_entropy`, `m H_{m-1} ≥ (m - 2) H_m + m H_1`.

Everything here is unconditional.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory MvPolynomial
open scoped ENNReal

namespace Parking

/-! ### Chain rule and mutual information -/

section Chain

variable {α β γ : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]

/-- The real-valued form of `ProbabilityTheory.cond_apply`:
`μ[t | s] = μ(s)⁻¹ μ(s ∩ t)`, also when `μ(s) = 0` (both sides then vanish). -/
theorem measureReal_cond_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {s : Set Ω}
    (hs : MeasurableSet s) (t : Set Ω) :
    (μ[|s]).real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  rw [measureReal_def, cond_apply hs μ t, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rfl

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype γ] in
/-- The multiplication rule `P(f = b, g = c) = P(f = b) P(g = c | f = b)` for a finite law on a
finite set, also when `P(f = b) = 0`. -/
theorem measureReal_inter_preimage_eq_mul (μ : Measure α) [IsFiniteMeasure μ] (f : α → β)
    (g : α → γ) (b : β) (c : γ) :
    μ.real (f ⁻¹' {b} ∩ g ⁻¹' {c}) =
      μ.real (f ⁻¹' {b}) * ((μ[|f ⁻¹' {b}]).map g).real {c} := by
  rw [map_measureReal_apply (measurable_of_finite g) (measurableSet_singleton c),
    measureReal_cond_apply μ (Set.toFinite _).measurableSet]
  by_cases h : μ.real (f ⁻¹' {b}) = 0
  · have h' : μ.real (f ⁻¹' {b} ∩ g ⁻¹' {c}) = 0 :=
      le_antisymm (h ▸ measureReal_mono Set.inter_subset_left) measureReal_nonneg
    rw [h', h, zero_mul]
  · rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- The law of total probability on a finite set: `∑_b P(f = b, t) = P(t)`. -/
theorem sum_measureReal_preimage_inter (μ : Measure α) [IsFiniteMeasure μ] (f : α → β)
    (t : Set α) : ∑ b, μ.real (f ⁻¹' {b} ∩ t) = μ.real t := by
  classical
  have h := measureReal_biUnion_finset (μ := μ) (s := Finset.univ)
    (f := fun b => f ⁻¹' {b} ∩ t) (fun b _ b' _ hbb' => ?_)
    (fun b _ => (Set.toFinite _).measurableSet)
  · rw [← h]
    congr 1
    ext x
    simp
  · refine Set.disjoint_left.2 fun x hx hx' => hbb' ?_
    exact hx.1.symm.trans hx'.1

/-- The chain rule for entropy, with the conditional entropy written as an average
([LS26, §3.1]): for random variables `f, g` on a finite probability space `(α, μ)`,
`H(g, f) = H(f) + ∑_b P(f = b) H(L(g | f = b))`, where `L(g | f = b)` is the image of the
conditional law `μ[|f ⁻¹' {b}]` under `g`. The terms with `P(f = b) = 0` vanish. -/
theorem entropy_map_prod_eq (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β)
    (g : α → γ) :
    entropy (μ.map fun x => (g x, f x)) =
      entropy (μ.map f) + ∑ b, μ.real (f ⁻¹' {b}) * entropy ((μ[|f ⁻¹' {b}]).map g) := by
  have hjoint (c : γ) (b : β) : (μ.map fun x => (g x, f x)).real {(c, b)} =
      μ.real (f ⁻¹' {b} ∩ g ⁻¹' {c}) := by
    rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _)]
    congr 1
    ext x
    simp [and_comm]
  have hf (b : β) : (μ.map f).real {b} = μ.real (f ⁻¹' {b}) :=
    map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _)
  have hsum (b : β) : Real.negMulLog (μ.real (f ⁻¹' {b})) *
      ∑ c, ((μ[|f ⁻¹' {b}]).map g).real {c} = Real.negMulLog (μ.real (f ⁻¹' {b})) := by
    by_cases hp : μ (f ⁻¹' {b}) = 0
    · rw [measureReal_def, hp, ENNReal.toReal_zero, Real.negMulLog_zero, zero_mul]
    · have := cond_isProbabilityMeasure (μ := μ) hp
      rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ, mul_one]
  simp only [entropy]
  rw [Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [hjoint, hf, measureReal_inter_preimage_eq_mul μ f g b, Real.negMulLog_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [mul_comm, hsum]

/-- For probability laws `μ ≪ ν` on a finite set, the real relative entropy is
`D(μ ‖ ν) = ∑ₓ μ(x) log (μ(x) / ν(x))`; this sum is nonnegative (Gibbs' inequality). -/
theorem toReal_klDiv_eq_sum_of_ac (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ x, μ.real {x} * Real.log (μ.real {x} / ν.real {x}) := by
  rw [klDiv_eq_sum_of_ac μ ν hac, ENNReal.toReal_ofReal]
  have h := sum_mul_sub_log_sum_exp_le_sum μ ν hac fun _ => 0
  have hν : ∑ x, ν.real {x} = 1 := by
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  simpa only [mul_zero, Finset.sum_const_zero, Real.exp_zero, mul_one, hν, Real.log_one,
    sub_zero] using h

/-- Mutual information as an average relative entropy ([LS26, Proposition 3.2]): for random
variables `f, g` on a finite probability space `(α, μ)`,
`∑_b P(f = b) D(L(g | f = b) ‖ L(g)) = H(g) + H(f) - H(g, f)`, the right side being the
mutual information `I(g; f)`. The terms with `P(f = b) = 0` vanish; for the others,
`L(g | f = b) ≪ L(g)`, so the relative entropies are finite. -/
theorem sum_mul_toReal_klDiv_cond (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β)
    (g : α → γ) :
    ∑ b, μ.real (f ⁻¹' {b}) * (klDiv ((μ[|f ⁻¹' {b}]).map g) (μ.map g)).toReal =
      entropy (μ.map g) + entropy (μ.map f) - entropy (μ.map fun x => (g x, f x)) := by
  have hg (c : γ) : (μ.map g).real {c} = μ.real (g ⁻¹' {c}) :=
    map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _)
  have key (b : β) : μ.real (f ⁻¹' {b}) * (klDiv ((μ[|f ⁻¹' {b}]).map g) (μ.map g)).toReal =
      -(μ.real (f ⁻¹' {b}) * entropy ((μ[|f ⁻¹' {b}]).map g)) -
        ∑ c, μ.real (f ⁻¹' {b} ∩ g ⁻¹' {c}) * Real.log ((μ.map g).real {c}) := by
    simp only [measureReal_inter_preimage_eq_mul μ f g b]
    by_cases hp : μ (f ⁻¹' {b}) = 0
    · simp only [measureReal_def, hp, ENNReal.toReal_zero, zero_mul, neg_zero,
        Finset.sum_const_zero, sub_zero]
    · have := cond_isProbabilityMeasure (μ := μ) hp
      have hac : (μ[|f ⁻¹' {b}]).map g ≪ μ.map g :=
        cond_absolutelyContinuous.map (measurable_of_finite g)
      rw [toReal_klDiv_eq_sum_of_ac _ _ hac, entropy, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      set r := ((μ[|f ⁻¹' {b}]).map g).real {c}
      rcases (measureReal_nonneg : 0 ≤ r).eq_or_lt with h0 | hr
      · have hr0 : r = 0 := h0.symm
        rw [hr0]
        simp only [zero_mul, mul_zero, Real.negMulLog_zero, neg_zero, sub_zero]
      · have ht := measureReal_singleton_pos_of_ac hac hr
        rw [Real.log_div hr.ne' ht.ne', Real.negMulLog]
        ring
  rw [Finset.sum_congr rfl fun b _ => key b, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_comm, entropy_map_prod_eq μ f g]
  simp only [← Finset.sum_mul, sum_measureReal_preimage_inter, ← hg]
  have hH : entropy (μ.map g) = -∑ c, (μ.map g).real {c} * Real.log ((μ.map g).real {c}) := by
    rw [entropy, ← Finset.sum_neg_distrib]
    simp only [Real.negMulLog, neg_mul]
  rw [hH]
  ring

/-- The chain rule `H(X) = H(f(X)) + ∑_b P(f(X) = b) H(L(X | f(X) = b))` for a law `μ` on a
finite set: the case `g = id` of `entropy_map_prod_eq`. -/
theorem entropy_eq_add_sum_cond (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) :
    entropy μ = entropy (μ.map f) + ∑ b, μ.real (f ⁻¹' {b}) * entropy (μ[|f ⁻¹' {b}]) := by
  have h := entropy_map_prod_eq μ f id
  simp only [Measure.map_id] at h
  rw [← h]
  exact (entropy_map_of_injective μ fun x y hxy => (Prod.mk.inj hxy).1).symm

end Chain

/-! ### Exchangeable laws and conditioning on the last coordinate -/

/-- For an exchangeable law on `[d]^N`, permuting the coordinates of a word does not change its
mass. -/
theorem IsExchangeableLaw.measureReal_singleton_comp {N d : ℕ} {μ : Measure (Fin N → Fin d)}
    (hμ : IsExchangeableLaw μ) (σ : Equiv.Perm (Fin N)) (ω : Fin N → Fin d) :
    μ.real {fun i => ω (σ i)} = μ.real {ω} := by
  have hinj : Function.Injective fun (x : Fin N → Fin d) (i : Fin N) => x (σ i) := by
    intro x y h
    funext i
    simpa using congrFun h (σ.symm i)
  conv_lhs => rw [← hμ σ]
  rw [map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton _)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact hinj.eq_iff

/-- For an exchangeable law `μ` on `[d]^N`, a permutation `σ` of the coordinates and any `F`,
`∑_ω μ(ω) F(ω ∘ σ) = ∑_ω μ(ω) F(ω)`. -/
theorem IsExchangeableLaw.sum_smul_comp {N d : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {μ : Measure (Fin N → Fin d)} (hμ : IsExchangeableLaw μ) (σ : Equiv.Perm (Fin N))
    (F : (Fin N → Fin d) → M) :
    ∑ ω, μ.real {ω} • F (fun i => ω (σ i)) = ∑ ω, μ.real {ω} • F ω := by
  let e : (Fin N → Fin d) ≃ (Fin N → Fin d) :=
    { toFun := fun ω i => ω (σ i)
      invFun := fun ω i => ω (σ.symm i)
      left_inv := fun ω => funext fun i => by simp
      right_inv := fun ω => funext fun i => by simp }
  calc ∑ ω, μ.real {ω} • F (fun i => ω (σ i)) = ∑ ω, μ.real {e ω} • F (e ω) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [show μ.real {e ω} = μ.real {ω} from hμ.measureReal_singleton_comp σ ω]
        rfl
    _ = ∑ ω, μ.real {ω} • F ω := e.sum_comp fun ω => μ.real {ω} • F ω

/-- The Leibniz rule for `∂_a ∏_{j ≤ m+1} x_{ω_j}`: it is
`∑_j ∂_a x_{ω_j} ∏_{i ≠ j} x_{ω_i}`, the coordinates other than `j` being listed as
`j.succAbove i` for `i : Fin m`. -/
theorem pderiv_prod_X {m d : ℕ} (a : Fin d) (ω : Fin (m + 1) → Fin d) :
    pderiv a (∏ j, X (ω j) : MvPolynomial (Fin d) ℝ) =
      ∑ j : Fin (m + 1), pderiv a (X (ω j)) * ∏ i : Fin m, X (ω (j.succAbove i)) := by
  induction m with
  | zero => rw [Fin.prod_univ_one, Fin.sum_univ_one, Fin.prod_univ_zero, mul_one]
  | succ m ih =>
    rw [Fin.prod_univ_succ, Derivation.leibniz, ih fun j => ω j.succ,
      Fin.sum_univ_succ (f := fun j : Fin (m + 2) =>
        pderiv a (X (ω j)) * ∏ i : Fin (m + 1), X (ω (j.succAbove i)))]
    simp only [Fin.zero_succAbove, smul_eq_mul, Finset.mul_sum]
    rw [add_comm, mul_comm (∏ i : Fin (m + 1), X (ω i.succ))]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.prod_univ_succ (f := fun i : Fin (m + 1) => X (ω (j.succ.succAbove i)))]
    simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
    ring

/-- The law `L(X_{[m]} | X_{m+1} = a)` of the first `m` coordinates of `X ∼ μ`, a law on
`[d]^{m+1}`, conditionally on the event that the last coordinate equals `a`. It is the zero
measure when this event is `μ`-null. -/
@[expose] noncomputable def condLastLaw {m d : ℕ} (μ : Measure (Fin (m + 1) → Fin d))
    (a : Fin d) : Measure (Fin m → Fin d) :=
  coordLaw (μ[|(fun x => x (Fin.last m)) ⁻¹' {a}]) (Nat.le_succ m)

/-- If the last coordinate equals `a` with positive probability, the conditional law
`L(X_{[m]} | X_{m+1} = a)` is a probability law. -/
theorem isProbabilityMeasure_condLastLaw {m d : ℕ} (μ : Measure (Fin (m + 1) → Fin d))
    [IsFiniteMeasure μ] {a : Fin d} (ha : 0 < μ.real ((fun x => x (Fin.last m)) ⁻¹' {a})) :
    IsProbabilityMeasure (condLastLaw μ a) := by
  have h0 : μ ((fun x => x (Fin.last m)) ⁻¹' {a}) ≠ 0 := fun h => by
    rw [measureReal_def, h, ENNReal.toReal_zero] at ha
    exact lt_irrefl _ ha
  have := cond_isProbabilityMeasure h0
  unfold condLastLaw coordLaw
  infer_instance

/-- Part of [LS26, Lemma 3.4(2)]: for an exchangeable law `μ` on `[d]^{m+1}`, the conditional
law `L(X_{[m]} | X_{m+1} = a)` is exchangeable. A permutation of the first `m` coordinates,
extended by fixing the last one, preserves `μ` and the event `{X_{m+1} = a}`. -/
theorem IsExchangeableLaw.condLastLaw {m d : ℕ} {μ : Measure (Fin (m + 1) → Fin d)}
    (hμ : IsExchangeableLaw μ) (a : Fin d) : IsExchangeableLaw (condLastLaw μ a) := by
  intro σ
  set τ := tauEquiv (Nat.le_succ m) σ
  set s := (fun x : Fin (m + 1) → Fin d => x (Fin.last m)) ⁻¹' {a}
  have hτ : τ (Fin.last m) = Fin.last m := by
    show (if h : (Fin.last m).val < m then _ else Fin.last m) = Fin.last m
    rw [dite_eq_right_iff.2 fun h => absurd h (by simp)]
  have hs : (fun x : Fin (m + 1) → Fin d => fun i => x (τ i)) ⁻¹' s = s := by
    ext x
    simp [s, hτ]
  have h1 : (μ.restrict s).map (fun x : Fin (m + 1) → Fin d => fun i => x (τ i)) =
      μ.restrict s := by
    conv_lhs => rw [← hs]
    rw [← Measure.restrict_map (measurable_of_finite _) (Set.toFinite s).measurableSet, hμ τ]
  have hcond : (μ[|s]).map (fun x : Fin (m + 1) → Fin d => fun i => x (τ i)) = μ[|s] := by
    rw [ProbabilityTheory.cond, Measure.map_smul _ (measurable_of_finite _).aemeasurable, h1]
  have hcomp : (fun y : Fin m → Fin d => fun i => y (σ i)) ∘
        (fun x : Fin (m + 1) → Fin d => fun i => x (Fin.castLE (Nat.le_succ m) i)) =
      (fun x : Fin (m + 1) → Fin d => fun i => x (Fin.castLE (Nat.le_succ m) i)) ∘
        (fun x : Fin (m + 1) → Fin d => fun i => x (τ i)) := by
    funext x i
    simp only [Function.comp_apply, τ, tauEquiv_castLE]
  show ((μ[|s]).map _).map _ = (μ[|s]).map _
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hcomp,
    ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hcond]

/-- The identity in the proof of [LS26, Lemma 3.4(2)]: for an exchangeable finite law `μ` on
`[d]^{m+1}`, the conditional law `L(X_{[m]} | X_{m+1} = a)` has count-generating polynomial
`∂_a h_μ / ((m + 1) P(X_{m+1} = a))`. Indeed
`∂_a ∏_j x_{ω_j} = ∑_{j : ω_j = a} ∏_{i ≠ j} x_{ω_i}`, and by exchangeability each of the
`m + 1` resulting sums equals the one for `j = m + 1`, which is
`P(X_{m+1} = a) h_{L(X_{[m]} | X_{m+1} = a)}`. When `P(X_{m+1} = a) = 0`, both sides
vanish. -/
theorem countPoly_condLastLaw {m d : ℕ} (μ : Measure (Fin (m + 1) → Fin d))
    [IsFiniteMeasure μ] (hμ : IsExchangeableLaw μ) (a : Fin d) :
    countPoly (condLastLaw μ a) =
      (((m : ℝ) + 1) * μ.real ((fun x => x (Fin.last m)) ⁻¹' {a}))⁻¹ •
        pderiv a (countPoly μ) := by
  set s := (fun x : Fin (m + 1) → Fin d => x (Fin.last m)) ⁻¹' {a}
  set p := μ.real s
  let G : (Fin (m + 1) → Fin d) → MvPolynomial (Fin d) ℝ := fun ω =>
    pderiv a (X (ω (Fin.last m))) * ∏ i : Fin m, X (ω i.castSucc)
  have hj (j : Fin (m + 1)) : ∑ ω, μ.real {ω} •
      (pderiv a (X (ω j)) * ∏ i : Fin m, X (ω (j.succAbove i)) : MvPolynomial (Fin d) ℝ) =
      ∑ ω, μ.real {ω} • G ω := by
    let G' : (Fin (m + 1) → Fin d) → MvPolynomial (Fin d) ℝ := fun η =>
      pderiv a (X (η 0)) * ∏ i : Fin m, X (η i.succ)
    have e1 := hμ.sum_smul_comp j.cycleRange.symm G'
    have e2 := hμ.sum_smul_comp (Fin.last m).cycleRange.symm G'
    simp only [G', Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ, Fin.succAbove_last]
      at e1 e2
    rw [e1, ← e2]
  have hderiv : pderiv a (countPoly μ) = ((m : ℝ) + 1) • ∑ ω, μ.real {ω} • G ω := by
    simp only [countPoly, map_sum, Derivation.map_smul, pderiv_prod_X, Finset.smul_sum]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, hj]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_succ]
  have hpt (ω : Fin (m + 1) → Fin d) : (μ[|s]).real {ω} •
      (∏ i : Fin m, X (ω (Fin.castLE (Nat.le_succ m) i)) : MvPolynomial (Fin d) ℝ) =
      p⁻¹ • (μ.real {ω} • G ω) := by
    rw [measureReal_cond_apply μ (Set.toFinite s).measurableSet]
    by_cases hω : ω (Fin.last m) = a
    · have h1 : s ∩ {ω} = {ω} := Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hω)
      simp only [G, h1, hω, pderiv_X_self, one_mul, smul_smul]
      rfl
    · have h1 : s ∩ {ω} = ∅ := Set.inter_singleton_eq_empty.2 hω
      simp only [G, h1, measureReal_empty, mul_zero, zero_smul, pderiv_X_of_ne hω, zero_mul,
        smul_zero]
  have hcp : countPoly (condLastLaw μ a) = ∑ ω, (μ[|s]).real {ω} •
      (∏ i : Fin m, X (ω (Fin.castLE (Nat.le_succ m) i)) : MvPolynomial (Fin d) ℝ) :=
    countPoly_map _ _
  rw [hcp, Finset.sum_congr rfl fun ω _ => hpt ω, ← Finset.smul_sum, hderiv, smul_smul]
  congr 1
  rw [mul_inv, mul_comm ((m : ℝ) + 1)⁻¹ p⁻¹, mul_assoc, inv_mul_cancel₀ (by positivity),
    mul_one]

/-- The complete log-concavity form of [LS26, Lemma 3.4(2)]: for an exchangeable finite law `μ`
on `[d]^{m+1}` with completely log-concave count-generating polynomial and a letter `a` with
`P(X_{m+1} = a) > 0`, the conditional law `L(X_{[m]} | X_{m+1} = a)` has a completely
log-concave count-generating polynomial, a positive multiple of `∂_a h_μ`. -/
theorem completelyLogConcave_countPoly_condLastLaw {m d : ℕ}
    (μ : Measure (Fin (m + 1) → Fin d)) [IsFiniteMeasure μ] (hμ : IsExchangeableLaw μ)
    (h : CompletelyLogConcave (countPoly μ)) {a : Fin d}
    (ha : 0 < μ.real ((fun x => x (Fin.last m)) ⁻¹' {a})) :
    CompletelyLogConcave (countPoly (condLastLaw μ a)) := by
  rw [countPoly_condLastLaw μ hμ a]
  exact (h.pderiv a).smul (inv_pos.2 (mul_pos (by positivity) ha))

/-! ### The strengthened Han inequality -/

/-- The entropy of the law of the first `k` coordinates depends only on `k`, not on the proof
of `k ≤ N` (used to identify `Fin (m - 1)` with `Fin n` when `m = n + 1`). -/
theorem entropy_coordLaw_congr {N d k l : ℕ} (μ : Measure (Fin N → Fin d)) (hk : k ≤ N)
    (hl : l ≤ N) (h : k = l) : entropy (coordLaw μ hk) = entropy (coordLaw μ hl) := by
  subst h
  rfl

/-- For an exchangeable law on `[d]^{n+1}`, deleting coordinate `j` leaves a vector with the
entropy of the first `n` coordinates: relabel `[n+1] ∖ {j}` by `j.succAbove` and use
exchangeability. -/
theorem IsExchangeableLaw.entropy_restrictCoordLaw_erase {n d : ℕ}
    {μ : Measure (Fin (n + 1) → Fin d)} (hμ : IsExchangeableLaw μ) (j : Fin (n + 1)) :
    entropy (restrictCoordLaw μ (Finset.univ.erase j)) =
      entropy (Parking.coordLaw μ (Nat.le_succ n)) := by
  let e : (↥(Finset.univ.erase j : Finset (Fin (n + 1))) → Fin d) → (Fin n → Fin d) :=
    fun y i => y ⟨j.succAbove i, Finset.mem_erase.2 ⟨Fin.succAbove_ne j i, Finset.mem_univ _⟩⟩
  have he : Function.Injective e := by
    intro y y' h
    funext ⟨k, hk⟩
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.1 hk).1
    exact congrFun h i
  rw [← entropy_map_of_injective _ he, restrictCoordLaw,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    ← hμ.map_succAbove_eq_coordLaw j]
  rfl

/-- [LS26, Lemma 3.7] in the exchangeable form, for `m = n + 2` coordinates:
`n H(X) + (n + 2) H(X_1) ≤ (n + 2) H(X_{[n+1]})`. The proof is the induction of
[LS26, Lemma 3.7] on `n`. For the step from `n` to `n + 1`, let `X` have law `μ` on
`[d]^{n+3}` and write `X = (Y, Z)` with `Y = X_{[n+2]}`, `Z = X_{n+3}`,
`ρ_z = L(Y | Z = z)` and `ν = L(Y)`. Averaging the induction hypothesis for the laws `ρ_z`
(`completelyLogConcave_countPoly_condLastLaw`) with the chain rule gives
`n (H(X) - H(Z)) + (n + 2) (H(Y_1, Z) - H(Z)) ≤ (n + 2) (H(Y) - H(Z))`, where
`H(Y_{[n+1]}, Z) = H(Y)` by exchangeability. The one-coordinate contraction
`(n + 2) D((ρ_z)_1 ‖ ν_1) ≤ D(ρ_z ‖ ν)` (`klDiv_coordMarginalLaw_le_of_completelyLogConcave`),
averaged over `z` with `sum_mul_toReal_klDiv_cond`, gives
`(n + 2) I(Y_1; Z) ≤ I(Y; Z)`. Adding the two inequalities, with `H(Y_1) = H(Z) = H(X_1)`,
gives the claim for `n + 1`. The base case `n = 0` is an equality. -/
theorem mul_entropy_coordLaw_ge_aux {d : ℕ} (n : ℕ) (μ : Measure (Fin (n + 2) → Fin d))
    [IsProbabilityMeasure μ] (hμ : IsExchangeableLaw μ)
    (h : CompletelyLogConcave (countPoly μ)) :
    (n : ℝ) * entropy μ + ((n : ℝ) + 2) * entropy (coordMarginalLaw μ ⟨0, by omega⟩) ≤
      ((n : ℝ) + 2) * entropy (coordLaw μ (Nat.le_succ (n + 1))) := by
  induction n with
  | zero =>
    have hinj : Function.Injective fun (y : Fin 1 → Fin d) => y 0 := by
      intro y y' hy
      funext i
      rw [Subsingleton.elim i 0]
      exact hy
    have h1 : entropy (coordLaw μ (Nat.le_succ 1)) =
        entropy (coordMarginalLaw μ ⟨0, by omega⟩) := by
      rw [← entropy_map_of_injective _ hinj, coordLaw,
        Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
      rfl
    rw [h1, Nat.cast_zero, zero_mul, zero_add]
  | succ n ih =>
    have hm1 : 1 ≤ n + 2 := by omega
    set Z : (Fin (n + 3) → Fin d) → Fin d := fun x => x (Fin.last (n + 2))
    set g : (Fin (n + 3) → Fin d) → (Fin (n + 2) → Fin d) :=
      fun x i => x (Fin.castLE (Nat.le_succ (n + 2)) i)
    set g0 : (Fin (n + 3) → Fin d) → Fin d := fun x => x ⟨0, by omega⟩
    set g2 : (Fin (n + 3) → Fin d) → (Fin (n + 1) → Fin d) :=
      fun x i => x (Fin.castLE (by omega) i)
    set ν := coordLaw μ (Nat.le_succ (n + 2)) with hν_def
    have : IsProbabilityMeasure ν := by
      rw [hν_def, coordLaw]
      infer_instance
    have hνg : ν = μ.map g := rfl
    have hρ (z : Fin d) : condLastLaw μ z = (μ[|Z ⁻¹' {z}]).map g := rfl
    have hρ0 (z : Fin d) : coordMarginalLaw (condLastLaw μ z) ⟨0, by omega⟩ =
        (μ[|Z ⁻¹' {z}]).map g0 := by
      rw [hρ, coordMarginalLaw,
        Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
      rfl
    have hρ2 (z : Fin d) : coordLaw (condLastLaw μ z) (Nat.le_succ (n + 1)) =
        (μ[|Z ⁻¹' {z}]).map g2 := by
      rw [hρ, coordLaw, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
      rfl
    have hν0 : coordMarginalLaw ν ⟨0, by omega⟩ = μ.map g0 := by
      rw [hνg, coordMarginalLaw,
        Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
      rfl
    have hμ0 : coordMarginalLaw μ ⟨0, by omega⟩ = μ.map g0 := rfl
    have hZ0 : entropy (μ.map Z) = entropy (μ.map g0) := by
      rw [show μ.map Z = μ.map g0 from hμ.coordMarginalLaw_eq (Fin.last (n + 2)) ⟨0, by omega⟩]
    -- chain rules
    have C1 := entropy_map_prod_eq μ Z g
    have C1' : entropy (μ.map fun x => (g x, Z x)) = entropy μ := by
      refine entropy_map_of_injective μ fun x y hxy => ?_
      simp only [Prod.mk.injEq] at hxy
      funext i
      induction i using Fin.lastCases with
      | last => exact hxy.2
      | cast i => exact congrFun hxy.1 i
    have C2 := entropy_map_prod_eq μ Z g0
    have C3 := entropy_map_prod_eq μ Z g2
    have C3' : entropy (μ.map fun x => (g2 x, Z x)) = entropy ν := by
      have he : Function.Injective fun q : (Fin (n + 1) → Fin d) × Fin d =>
          (Fin.snoc (α := fun _ => Fin d) q.1 q.2 : Fin (n + 2) → Fin d) :=
        fun q q' hq => Prod.ext (Fin.snoc_injective2 hq).1 (Fin.snoc_injective2 hq).2
      rw [← entropy_map_of_injective _ he,
        Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hν_def,
        ← hμ.map_succAbove_eq_coordLaw (Fin.last (n + 1)).castSucc]
      congr 2
      funext x i
      simp only [Function.comp_apply]
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.succAbove_castSucc_self, Fin.succ_last]
      | cast i =>
        rw [Fin.snoc_castSucc, Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last i)]
        rfl
    -- mutual informations
    have K1 := sum_mul_toReal_klDiv_cond μ Z g
    have K2 := sum_mul_toReal_klDiv_cond μ Z g0
    -- induction hypothesis, averaged over the last coordinate
    have hIH (z : Fin d) : (n : ℝ) * (μ.real (Z ⁻¹' {z}) * entropy ((μ[|Z ⁻¹' {z}]).map g)) +
        ((n : ℝ) + 2) * (μ.real (Z ⁻¹' {z}) * entropy ((μ[|Z ⁻¹' {z}]).map g0)) ≤
        ((n : ℝ) + 2) * (μ.real (Z ⁻¹' {z}) * entropy ((μ[|Z ⁻¹' {z}]).map g2)) := by
      rcases (measureReal_nonneg : 0 ≤ μ.real (Z ⁻¹' {z})).eq_or_lt with h0 | hpos
      · simp only [← h0, zero_mul, mul_zero, add_zero, le_refl]
      · have := isProbabilityMeasure_condLastLaw μ hpos
        have hih := ih (condLastLaw μ z) (hμ.condLastLaw z)
          (completelyLogConcave_countPoly_condLastLaw μ hμ h hpos)
        rw [hρ0, hρ2, hρ] at hih
        have := mul_le_mul_of_nonneg_left hih hpos.le
        linarith
    -- one-coordinate contraction, averaged over the last coordinate
    have hL (z : Fin d) : ((n : ℝ) + 2) *
        (μ.real (Z ⁻¹' {z}) * (klDiv ((μ[|Z ⁻¹' {z}]).map g0) (μ.map g0)).toReal) ≤
        μ.real (Z ⁻¹' {z}) * (klDiv ((μ[|Z ⁻¹' {z}]).map g) (μ.map g)).toReal := by
      rcases (measureReal_nonneg : 0 ≤ μ.real (Z ⁻¹' {z})).eq_or_lt with h0 | hpos
      · simp only [← h0, zero_mul, mul_zero, le_refl]
      · have hprob := isProbabilityMeasure_condLastLaw μ hpos
        have : IsProbabilityMeasure ((μ[|Z ⁻¹' {z}]).map g) := hprob
        have hk := klDiv_coordMarginalLaw_le_of_completelyLogConcave hm1 (condLastLaw μ z) ν
          (hμ.condLastLaw z) (IsExchangeableLaw.coordLaw μ hμ _)
          (completelyLogConcave_countPoly_coordLaw μ hμ h _)
        rw [hρ0, hν0, hρ, hνg] at hk
        have hac : (μ[|Z ⁻¹' {z}]).map g ≪ μ.map g :=
          cond_absolutelyContinuous.map (measurable_of_finite g)
        have hfin : klDiv ((μ[|Z ⁻¹' {z}]).map g) (μ.map g) ≠ ∞ := by
          rw [klDiv_eq_sum_of_ac _ _ hac]
          exact ENNReal.ofReal_ne_top
        have hk' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) hk
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast] at hk'
        have hn : (0 : ℝ) < n + 2 := by positivity
        have h2 : ((n : ℝ) + 2) * (klDiv ((μ[|Z ⁻¹' {z}]).map g0) (μ.map g0)).toReal ≤
            (klDiv ((μ[|Z ⁻¹' {z}]).map g) (μ.map g)).toReal := by
          rw [← le_inv_mul_iff₀ hn]
          push_cast at hk'
          exact hk'
        have := mul_le_mul_of_nonneg_left h2 hpos.le
        linarith
    have SIH := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hIH z
    have SL := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hL z
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at SIH
    rw [← Finset.mul_sum] at SL
    have eA : ∑ z, μ.real (Z ⁻¹' {z}) * entropy ((μ[|Z ⁻¹' {z}]).map g) =
        entropy μ - entropy (μ.map Z) := by linarith
    have eB : ∑ z, μ.real (Z ⁻¹' {z}) * entropy ((μ[|Z ⁻¹' {z}]).map g0) =
        entropy (μ.map fun x => (g0 x, Z x)) - entropy (μ.map Z) := by linarith
    have eC : ∑ z, μ.real (Z ⁻¹' {z}) * entropy ((μ[|Z ⁻¹' {z}]).map g2) =
        entropy ν - entropy (μ.map Z) := by linarith
    rw [eA, eB, eC] at SIH
    rw [K1, K2, ← hνg, C1', hZ0] at SL
    rw [hZ0] at SIH
    rw [hμ0]
    push_cast
    linarith

/-- The form of [LS26, Lemma 3.7] used in `lem:sample_entropy`, under
complete log-concavity: for `m ≥ 2` and an exchangeable law `μ` on `[d]^m` with completely
log-concave count-generating polynomial, `(m - 2) H_m + m H_1 ≤ m H_{m-1}`, where `H_k` is the
entropy of the first `k` coordinates. Every deletion law has the entropy `H_{m-1}` and every
coordinate law equals the first one, by exchangeability. -/
theorem mul_entropy_coordLaw_ge_of_completelyLogConcave {m d : ℕ} (hm : 2 ≤ m)
    (μ : Measure (Fin m → Fin d)) [IsProbabilityMeasure μ] (hμ : IsExchangeableLaw μ)
    (h : CompletelyLogConcave (countPoly μ)) :
    ((m : ℝ) - 2) * entropy μ + m * entropy (coordMarginalLaw μ ⟨0, by omega⟩) ≤
      m * entropy (coordLaw μ (Nat.sub_le m 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rw [entropy_coordLaw_congr μ (Nat.sub_le (n + 2) 1) (Nat.le_succ (n + 1)) (by omega)]
  have := mul_entropy_coordLaw_ge_aux n μ hμ h
  push_cast
  linarith

/-- The complete log-concavity analogue of [LS26, Lemma 3.7], proved without external input:
for `m ≥ 2` and an exchangeable probability law `μ` on `[d]^m` whose count-generating
polynomial is completely log-concave, `X ∼ μ` satisfies the strengthened Han inequality
`(m - 2) H(X) + ∑_j H(X_j) ≤ ∑_j H(X_{[m] ∖ j})`. -/
theorem strongHan_of_completelyLogConcave {m d : ℕ} (hm : 2 ≤ m) (μ : Measure (Fin m → Fin d))
    [IsProbabilityMeasure μ] (hμ : IsExchangeableLaw μ)
    (h : CompletelyLogConcave (countPoly μ)) :
    ((m : ℝ) - 2) * entropy μ + ∑ j, entropy (coordMarginalLaw μ j) ≤
      ∑ j, entropy (restrictCoordLaw μ (Finset.univ.erase j)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h1 : ∑ j, entropy (coordMarginalLaw μ j) =
      ((n + 1 : ℕ) : ℝ) * entropy (coordMarginalLaw μ ⟨0, by omega⟩) := by
    rw [Finset.sum_congr rfl fun j _ =>
        congrArg entropy (hμ.coordMarginalLaw_eq j ⟨0, by omega⟩),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ∑ j, entropy (restrictCoordLaw μ (Finset.univ.erase j)) =
      ((n + 1 : ℕ) : ℝ) * entropy (coordLaw μ (Nat.sub_le (n + 1) 1)) := by
    rw [Finset.sum_congr rfl fun j _ => hμ.entropy_restrictCoordLaw_erase j, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      entropy_coordLaw_congr μ (Nat.sub_le (n + 1) 1) (Nat.le_succ n) (by omega)]
  rw [h1, h2]
  exact mul_entropy_coordLaw_ge_of_completelyLogConcave hm μ hμ h

/-- [LS26, Lemma 3.7] with its genuine Lorentzian hypothesis and displayed
sum over deletions. The cited interface is proved internally through the
algebraic-to-complete implication. -/
theorem strongHan_of_lorentzian {m d : ℕ} (hm : 2 ≤ m) (μ : Measure (Fin m → Fin d))
    [IsProbabilityMeasure μ] (hμ : IsExchangeableLaw μ)
    (h : Lorentzian m (countPoly μ)) :
    ((m : ℝ) - 2) * entropy μ + ∑ j, entropy (coordMarginalLaw μ j) ≤
      ∑ j, entropy (restrictCoordLaw μ (Finset.univ.erase j)) :=
  strongHan_of_completelyLogConcave hm μ hμ h.completelyLogConcave

end Parking

end
