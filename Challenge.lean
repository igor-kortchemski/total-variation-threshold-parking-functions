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

public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Parking: three approved theorem statements

Palomar Challenge with three deliberate theorem proof holes, explicitly authorized
for this export. Solution imports complete proofs of the same three statements.
The implementation library contains no proof holes.

Coordinates and values are zero based: a Lean value `j : Fin n` represents the
paper's value `j + 1`. The positive size is `n : ℕ+`. The laws below are the actual
uniform parking law and its coordinate projections, not abstract stand-ins.
The profile includes the infinite endpoint in `ℝ≥0∞`; relative entropy also
has values in `ℝ≥0∞`.
-/

public section

namespace Parking

open scoped BigOperators


@[expose] def isParkingFunction {n : ℕ+} (a : Fin n → Fin n) : Prop :=
  ∀ j : Fin n, j.val + 1 ≤ (Finset.univ.filter (fun i => a i ≤ j)).card

@[expose] def ParkingFunction (n : ℕ+) :=
  {a : Fin n → Fin n // isParkingFunction a}

theorem isParkingFunction_zero (n : ℕ+) :
    isParkingFunction (fun _ : Fin n => (0 : Fin n)) := by
  intro j
  change j.val + 1 ≤ (Finset.univ.filter (fun _ : Fin n => (0 : Fin n) ≤ j)).card
  rw [Finset.filter_eq_self.mpr (fun _ _ => Fin.zero_le j), Finset.card_fin]
  exact Nat.succ_le_of_lt j.isLt

theorem parkingFunction_nonempty (n : ℕ+) : Nonempty (ParkingFunction n) :=
  ⟨⟨fun _ => 0, isParkingFunction_zero n⟩⟩

end Parking

end

/- Reproduce the original module boundary: Lean's auxiliary-proof cache is local
to elaboration and is not serialized by imports. No declaration is changed. -/
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

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

noncomputable def tvDist {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) : ℝ :=
  2⁻¹ * ∑ x, |(P {x} : ℝ) - (Q {x} : ℝ)|

noncomputable def uniformLaw (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] : ProbabilityMeasure α :=
  ⟨uniformOn Set.univ, isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty⟩

noncomputable def uniformParking (n : ℕ+) : ProbabilityMeasure (ParkingFunction n) :=
  uniformLaw (ParkingFunction n)

def firstCoords (n : ℕ+) (k : ℕ) (hk : k ≤ n) (a : ParkingFunction n) : Fin k → Fin n :=
  fun r => a.1 (Fin.castLE hk r)

noncomputable def firstCoordsLaw (n : ℕ+) (k : ℕ) (hk : k ≤ n) :
    ProbabilityMeasure (Fin k → Fin n) :=
  (uniformParking n).map (firstCoords n k hk)

noncomputable def uniformProduct (n : ℕ+) (k : ℕ) : ProbabilityMeasure (Fin k → Fin n) :=
  ProbabilityMeasure.pi fun _ : Fin k => uniformLaw (Fin n)

def firstCoord (n : ℕ+) (a : ParkingFunction n) : Fin n :=
  a.1 ⟨0, n.pos⟩

noncomputable def marginal (n : ℕ+) : ProbabilityMeasure (Fin n) :=
  (uniformParking n).map (firstCoord n)

noncomputable def marginalProduct (n : ℕ+) (k : ℕ) : ProbabilityMeasure (Fin k → Fin n) :=
  ProbabilityMeasure.pi fun _ : Fin k => marginal n

noncomputable def profile (lam : ℝ≥0∞) : ℝ :=
  if lam = ∞ then 1
  else 2 * cdf (gaussianReal 0 1) (√(lam.toReal / Real.pi)) - 1

end Parking

end

/- Reproduce the original module boundary: Lean's auxiliary-proof cache is local
to elaboration and is not serialized by imports. No declaration is changed. -/
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

public section

namespace Parking

theorem tvDist_firstCoordsLaw_bounds :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → ∀ hkn : k ≤ n,
        √((k : ℝ) * Real.log ((k : ℝ) + 1) /
            (C * (n : ℝ) + (k : ℝ) * Real.log ((k : ℝ) + 1)))
          ≤ tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ∧
        tvDist (firstCoordsLaw n k hkn) (uniformProduct n k)
          ≤ min 1 (C * √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ))) :=
  by sorry

end Parking

end

/- Reproduce the original module boundary: Lean's auxiliary-proof cache is local
to elaboration and is not serialized by imports. No declaration is changed. -/
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

public section

open Filter Topology
open scoped ENNReal

namespace Parking

theorem tendsto_tvDist_firstCoordsLaw (k : ℕ+ → ℕ) (hk : ∀ n, 1 ≤ k n)
    (hkn : ∀ n, k n ≤ n) (lam : ℝ≥0∞)
    (hlim : Tendsto (fun n : ℕ+ => ENNReal.ofReal ((k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 lam)) :
    Tendsto (fun n : ℕ+ => tvDist (firstCoordsLaw n (k n) (hkn n)) (uniformProduct n (k n)))
      atTop (𝓝 (profile lam)) :=
  by sorry

end Parking

end

/- Reproduce the original module boundary: Lean's auxiliary-proof cache is local
to elaboration and is not serialized by imports. No declaration is changed. -/
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace Parking

theorem klDiv_tvDist_firstCoordsLaw_le (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    klDiv (firstCoordsLaw n k hkn : Measure (Fin k → Fin n))
        (marginalProduct n k : Measure (Fin k → Fin n))
      ≤ ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) *
          Real.log (n : ℝ)) ∧
    tvDist (firstCoordsLaw n k hkn) (marginalProduct n k)
      ≤ √((k : ℝ) * ((k : ℝ) - 1) * Real.log (n : ℝ) /
          (2 * (n : ℝ) * ((n : ℝ) - 1))) :=
  by sorry

end Parking

end
