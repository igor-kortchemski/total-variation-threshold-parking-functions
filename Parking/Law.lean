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

public import Parking.Basic
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Laws of the first coordinates of a uniform parking function

Source-facing definitions for `parking_threshold.tex`: the uniform law of `π_n` on
parking functions, the laws `P_{n,k}`, `Q_{n,k}`, `μ_n` and `μ_n^{⊗k}`, the total
variation distance between probability laws on a finite set, and the limiting profile
`F`. The lemmas give the explicit formula of each law, show that `μ_n^{⊗k}` charges
every point, and relate the Lean conventions to those of the manuscript.

Conventions inherited from `Parking.Basic`: the size is `n : ℕ+`; the Lean
coordinate `r : Fin k` is the source coordinate `r + 1`, and the Lean value
`j : Fin n` is the source value `j + 1`. Total variation and relative entropy are
invariant under this simultaneous relabelling of both laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace Parking

instance (n : ℕ+) : DecidablePred (isParkingFunction (n := n)) := fun a => by
  unfold isParkingFunction
  infer_instance

instance (n : ℕ+) : Fintype (ParkingFunction n) :=
  inferInstanceAs (Fintype {a : Fin n → Fin n // isParkingFunction a})

instance (n : ℕ+) : Nonempty (ParkingFunction n) :=
  parkingFunction_nonempty n

instance (n : ℕ+) : MeasurableSpace (ParkingFunction n) :=
  inferInstanceAs (MeasurableSpace {a : Fin n → Fin n // isParkingFunction a})

instance (n : ℕ+) : MeasurableSingletonClass (ParkingFunction n) :=
  Subtype.instMeasurableSingletonClass

/-- Total variation distance between two probability laws on a finite set,
`d_TV(P, Q) = ½ ∑ₓ |P(x) - Q(x)|` (source line 99). The binder
`MeasurableSingletonClass α` makes the space discrete, so that `P {x}` is the mass of
the atom `x`. -/
noncomputable def tvDist {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) : ℝ :=
  2⁻¹ * ∑ x, |(P {x} : ℝ) - (Q {x} : ℝ)|

/-- The uniform law on a finite nonempty type: counting measure normalized by the
cardinality. -/
noncomputable def uniformLaw (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] : ProbabilityMeasure α :=
  ⟨uniformOn Set.univ, isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty⟩

/-- The law of `π_n`, a uniform parking function of size `n` (source line 72). -/
noncomputable def uniformParking (n : ℕ+) : ProbabilityMeasure (ParkingFunction n) :=
  uniformLaw (ParkingFunction n)

/-- The first `k` coordinates `(π(1), …, π(k))` of a parking function. -/
def firstCoords (n : ℕ+) (k : ℕ) (hk : k ≤ n) (a : ParkingFunction n) : Fin k → Fin n :=
  fun r => a.1 (Fin.castLE hk r)

/-- `P_{n,k}`: the law of the first `k` coordinates of `π_n` (source line 75). -/
noncomputable def firstCoordsLaw (n : ℕ+) (k : ℕ) (hk : k ≤ n) :
    ProbabilityMeasure (Fin k → Fin n) :=
  (uniformParking n).map (firstCoords n k hk)

/-- `Q_{n,k} = U_n^{⊗k}`, with `U_n` the uniform law on `[n]` (source lines 73–76). -/
noncomputable def uniformProduct (n : ℕ+) (k : ℕ) : ProbabilityMeasure (Fin k → Fin n) :=
  ProbabilityMeasure.pi fun _ : Fin k => uniformLaw (Fin n)

/-- The first coordinate `π(1)` of a parking function. -/
def firstCoord (n : ℕ+) (a : ParkingFunction n) : Fin n :=
  a.1 ⟨0, n.pos⟩

/-- `μ_n`: the law of the first coordinate `π_n(1)` (source line 132). -/
noncomputable def marginal (n : ℕ+) : ProbabilityMeasure (Fin n) :=
  (uniformParking n).map (firstCoord n)

theorem measurable_firstCoords (n : ℕ+) (k : ℕ) (hk : k ≤ n) :
    Measurable (firstCoords n k hk) :=
  measurable_of_finite _

theorem measurable_firstCoord (n : ℕ+) : Measurable (firstCoord n) :=
  measurable_of_finite _

/-- `μ_n^{⊗k}` (source line 139). -/
noncomputable def marginalProduct (n : ℕ+) (k : ℕ) : ProbabilityMeasure (Fin k → Fin n) :=
  ProbabilityMeasure.pi fun _ : Fin k => marginal n

/-- The limiting profile `F(λ) = 2Φ(√(λ/π)) - 1` for `0 ≤ λ < ∞` and `F(∞) = 1`,
where `Φ` is the standard normal distribution function (source lines 105–110). -/
noncomputable def profile (lam : ℝ≥0∞) : ℝ :=
  if lam = ∞ then 1
  else 2 * cdf (gaussianReal 0 1) (√(lam.toReal / Real.pi)) - 1

/-! ### Explicit formulas: the laws are the source objects -/

/-- The uniform law gives each event its proportion of elements. -/
theorem uniformLaw_apply {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Finset α) :
    (uniformLaw α s : ℝ) = s.card / Fintype.card α := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  change (uniformOn Set.univ : Measure α).real s = _
  simp [Measure.real, uniformOn_univ, Measure.count_apply_finset, ENNReal.toReal_div]

/-- `P_{n,k}(x)` is the proportion of parking functions whose first `k`
coordinates are `x`. -/
theorem firstCoordsLaw_apply_singleton (n : ℕ+) (k : ℕ) (hk : k ≤ n) (x : Fin k → Fin n) :
    (firstCoordsLaw n k hk {x} : ℝ) =
      (Finset.univ.filter fun a => firstCoords n k hk a = x).card /
        Fintype.card (ParkingFunction n) := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, firstCoordsLaw,
    ProbabilityMeasure.toMeasure_map,
    map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton x),
    ProbabilityMeasure.measureReal_eq_coe_coeFn]
  have h : firstCoords n k hk ⁻¹' {x} =
      ↑(Finset.univ.filter fun a => firstCoords n k hk a = x) := by
    ext a; simp
  rw [h]
  exact uniformLaw_apply _

/-- `μ_n(j)` is the proportion of parking functions whose first coordinate is `j`. -/
theorem marginal_apply_singleton (n : ℕ+) (j : Fin n) :
    (marginal n {j} : ℝ) =
      (Finset.univ.filter fun a => firstCoord n a = j).card /
        Fintype.card (ParkingFunction n) := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, marginal,
    ProbabilityMeasure.toMeasure_map,
    map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton j),
    ProbabilityMeasure.measureReal_eq_coe_coeFn]
  have h : firstCoord n ⁻¹' {j} = ↑(Finset.univ.filter fun a => firstCoord n a = j) := by
    ext a; simp
  rw [h]
  exact uniformLaw_apply _

private theorem singleton_eq_univ_pi {k : ℕ} {β : Type*} (x : Fin k → β) :
    ({x} : Set (Fin k → β)) = Set.univ.pi fun r => {x r} := by
  ext y; simp [funext_iff]

/-- `Q_{n,k}(x) = n^{-k}`. -/
theorem uniformProduct_apply_singleton (n : ℕ+) (k : ℕ) (x : Fin k → Fin n) :
    (uniformProduct n k {x} : ℝ) = 1 / (n : ℝ) ^ k := by
  rw [singleton_eq_univ_pi, uniformProduct, ProbabilityMeasure.pi_pi]
  push_cast
  have h (r : Fin k) : (uniformLaw (Fin n) {x r} : ℝ) = 1 / (n : ℝ) := by
    simpa using uniformLaw_apply ({x r} : Finset (Fin n))
  simp [h]

/-- `μ_n^{⊗k}(x) = ∏_r μ_n(x_r)`. -/
theorem marginalProduct_apply_singleton (n : ℕ+) (k : ℕ) (x : Fin k → Fin n) :
    (marginalProduct n k {x} : ℝ) = ∏ r, (marginal n {x r} : ℝ) := by
  rw [singleton_eq_univ_pi, marginalProduct, ProbabilityMeasure.pi_pi]
  push_cast
  rfl

/-- Every preference `j` is the first coordinate of some parking function: put `j` first
and the minimal preference at every other coordinate. -/
theorem exists_firstCoord_eq (n : ℕ+) (j : Fin n) :
    ∃ a : ParkingFunction n, firstCoord n a = j := by
  classical
  let w : Fin n → Fin n := fun i => if i = ⟨0, n.pos⟩ then j else ⟨0, n.pos⟩
  refine ⟨⟨w, ?_⟩, by simp [firstCoord, w]⟩
  intro t
  by_cases ht : (t : ℕ) + 1 = (n : ℕ)
  · have hall : (Finset.univ.filter fun i => w i ≤ t) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Fin.le_def.2 (by have := (w i).isLt; omega)
    rw [hall, Finset.card_univ, Fintype.card_fin]
    omega
  · have hsub : Finset.univ.erase (⟨0, n.pos⟩ : Fin n) ⊆
        Finset.univ.filter fun i => w i ≤ t := by
      intro i hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, w, hi, ↓reduceIte]
      exact Fin.le_def.2 (Nat.zero_le _)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin] at hcard
    have := t.isLt
    omega

/-- `μ_n` charges every point of `[n]`. -/
theorem marginal_apply_singleton_pos (n : ℕ+) (j : Fin n) : 0 < (marginal n {j} : ℝ) := by
  rw [marginal_apply_singleton]
  obtain ⟨a, ha⟩ := exists_firstCoord_eq n j
  apply div_pos
  · exact_mod_cast Finset.card_pos.2 ⟨a, by simp [ha]⟩
  · exact_mod_cast Fintype.card_pos

/-- `μ_n^{⊗k}` charges every point of `[n]^k`. -/
theorem marginalProduct_apply_singleton_ne_zero (n : ℕ+) (k : ℕ) (x : Fin k → Fin n) :
    (marginalProduct n k : Measure (Fin k → Fin n)) {x} ≠ 0 := by
  have h : 0 < (marginalProduct n k {x} : ℝ) := by
    rw [marginalProduct_apply_singleton]
    exact Finset.prod_pos fun r _ => marginal_apply_singleton_pos n (x r)
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  have h' : (marginalProduct n k {x} : ℝ≥0) ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  exact_mod_cast h'

/-! ### Correspondence with the source conventions -/

/-- `isParkingFunction` is the source condition (lines 66–67) after the value shift
`x_i = a_i + 1`. -/
theorem isParkingFunction_iff_one_based {n : ℕ+} (a : Fin n → Fin n) :
    isParkingFunction a ↔ ∀ j : ℕ, 1 ≤ j → j ≤ (n : ℕ) →
      j ≤ (Finset.univ.filter fun i : Fin n => (a i : ℕ) + 1 ≤ j).card := by
  constructor
  · intro h j hj1 hjn
    have hfil : (Finset.univ.filter fun i => a i ≤ (⟨j - 1, by omega⟩ : Fin n)) =
        (Finset.univ.filter fun i : Fin n => (a i : ℕ) + 1 ≤ j) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]; omega
    have := h ⟨j - 1, by omega⟩
    rw [hfil] at this
    simp only at this
    omega
  · intro h j
    have hfil : (Finset.univ.filter fun i => a i ≤ j) =
        (Finset.univ.filter fun i : Fin n => (a i : ℕ) + 1 ≤ j.val + 1) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]; omega
    rw [hfil]
    exact h (j.val + 1) (by omega) (by omega)

/-- For a nonnegative sequence, convergence of `ENNReal.ofReal (f n)` to `λ ∈ [0, ∞]`
means `f n → +∞` if `λ = ∞`, and `f n → λ` otherwise. This is how the hypothesis of
`thm:profile` is encoded. -/
theorem tendsto_ofReal_iff (f : ℕ+ → ℝ) (hf : ∀ n, 0 ≤ f n) (lam : ℝ≥0∞) :
    Tendsto (fun n => ENNReal.ofReal (f n)) atTop (𝓝 lam) ↔
      (lam = ∞ ∧ Tendsto f atTop atTop) ∨
        (∃ l : ℝ, 0 ≤ l ∧ lam = ENNReal.ofReal l ∧ Tendsto f atTop (𝓝 l)) := by
  constructor
  · intro h
    by_cases hl : lam = ∞
    · subst hl; exact Or.inl ⟨rfl, ENNReal.tendsto_ofReal_nhds_top.1 h⟩
    · right
      refine ⟨lam.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hl).symm, ?_⟩
      have := (ENNReal.tendsto_toReal hl).comp h
      simpa [Function.comp_def, ENNReal.toReal_ofReal (hf _)] using this
  · rintro (⟨rfl, h⟩ | ⟨l, -, rfl, h⟩)
    · exact ENNReal.tendsto_ofReal_nhds_top.2 h
    · exact ENNReal.tendsto_ofReal h

/-- The sequence in the hypothesis of `thm:profile` is nonnegative. -/
theorem kLogDiv_nonneg (k : ℕ+ → ℕ) (n : ℕ+) :
    0 ≤ (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ) := by
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg this)) (by linarith)

/-- On a finite discrete space and for a reference law of full support, Mathlib's `klDiv`
is the source formula `∑ₓ P(x) log (P(x) / Q(x))` with natural logarithm (line 129). -/
theorem klDiv_eq_sum {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ x, ν {x} ≠ 0) :
    klDiv μ ν = ENNReal.ofReal (∑ x, μ.real {x} * Real.log (μ.real {x} / ν.real {x})) := by
  have hac : μ ≪ ν := by
    intro s hs
    have : s = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact hν x (measure_mono_null (Set.singleton_subset_iff.mpr hx) hs)
    simp [this]
  rw [klDiv_of_ac_of_integrable hac Integrable.of_finite]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_fintype Integrable.of_finite]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_eq_mul, llr]
  congr 2
  have h := Measure.setLIntegral_rnDeriv hac {x}
  rw [lintegral_singleton] at h
  have hr : μ.rnDeriv ν x = μ {x} / ν {x} :=
    (ENNReal.eq_div_iff (hν x) (measure_ne_top _ _)).mpr (by rw [mul_comm]; exact h)
  rw [hr, ENNReal.toReal_div]
  rfl

/-- For the laws of `prop:decoupling`, Mathlib's `klDiv` is the source formula
`∑ₓ P(x) log (P(x) / Q(x))` (line 129), since `μ_n^{⊗k}` charges every point. -/
theorem klDiv_firstCoordsLaw_marginalProduct (n : ℕ+) (k : ℕ) (hk : k ≤ n) :
    klDiv (firstCoordsLaw n k hk : Measure (Fin k → Fin n))
        (marginalProduct n k : Measure (Fin k → Fin n)) =
      ENNReal.ofReal (∑ x, (firstCoordsLaw n k hk {x} : ℝ) *
        Real.log ((firstCoordsLaw n k hk {x} : ℝ) / (marginalProduct n k {x} : ℝ))) := by
  rw [klDiv_eq_sum _ _ (marginalProduct_apply_singleton_ne_zero n k)]
  simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn]

end Parking

end
