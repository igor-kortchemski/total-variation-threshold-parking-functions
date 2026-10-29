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

/-!
# Generic facts on the total variation distance

This module collects elementary facts on
`Parking.tvDist`, the total variation distance `d_TV(P, Q) = ½ ∑ₓ |P(x) - Q(x)|` between two
probability laws on a finite discrete space (`thm:main`):

* the masses of the atoms sum to one (`sum_coe_apply_singleton`);
* `d_TV` is symmetric and satisfies the triangle inequality (`tvDist_comm`,
  `tvDist_triangle`, `abs_tvDist_sub_tvDist_le`);
* `d_TV(P, Q) = 1 - ∑ₓ min (P(x), Q(x))` (`tvDist_eq_one_sub_sum_min`), hence `d_TV ≤ 1`
  (`tvDist_le_one`);
* if `P(x) = Q(x) ρ(x)` for all `x`, then `d_TV(P, Q) = ∑ₓ Q(x) max (1 - ρ(x), 0)`
  (`tvDist_eq_sum_mul_max`).

Nonnegativity of `d_TV` is `Parking.tvDist_nonneg`, in `Parking.Pinsker`.
-/

public section

open MeasureTheory

namespace Parking

/-- The masses of the atoms of a probability law on a finite discrete space sum to one. -/
theorem sum_coe_apply_singleton {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P : ProbabilityMeasure α) : ∑ x, (P {x} : ℝ) = 1 := by
  simp only [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

/-- The total variation distance is symmetric. -/
theorem tvDist_comm {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) : tvDist P Q = tvDist Q P := by
  unfold tvDist
  congr 1
  exact Finset.sum_congr rfl fun x _ => abs_sub_comm _ _

/-- The triangle inequality for the total variation distance. -/
theorem tvDist_triangle {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q R : ProbabilityMeasure α) :
    tvDist P R ≤ tvDist P Q + tvDist Q R := by
  unfold tvDist
  rw [← mul_add, ← Finset.sum_add_distrib]
  gcongr with x
  exact abs_sub_le _ _ _

/-- The total variation distance to a fixed law is `1`-Lipschitz:
`|d_TV(P, R) - d_TV(Q, R)| ≤ d_TV(P, Q)`. -/
theorem abs_tvDist_sub_tvDist_le {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q R : ProbabilityMeasure α) :
    |tvDist P R - tvDist Q R| ≤ tvDist P Q := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [tvDist_triangle P Q R]
  · linarith [tvDist_triangle Q P R, tvDist_comm P Q]

/-- `d_TV(P, Q) = 1 - ∑ₓ min (P(x), Q(x))`. -/
theorem tvDist_eq_one_sub_sum_min {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) :
    tvDist P Q = 1 - ∑ x, min (P {x} : ℝ) (Q {x} : ℝ) := by
  have key : ∀ x, min (P {x} : ℝ) (Q {x} : ℝ) =
      ((P {x} : ℝ) + (Q {x} : ℝ) - |(P {x} : ℝ) - (Q {x} : ℝ)|) / 2 := by
    intro x
    rcases le_total (P {x} : ℝ) (Q {x} : ℝ) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      ring
  unfold tvDist
  rw [Finset.sum_congr rfl fun x _ => key x, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_coe_apply_singleton, sum_coe_apply_singleton]
  ring

/-- The total variation distance is at most one. -/
theorem tvDist_le_one {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) : tvDist P Q ≤ 1 := by
  rw [tvDist_eq_one_sub_sum_min]
  have : 0 ≤ ∑ x, min (P {x} : ℝ) (Q {x} : ℝ) :=
    Finset.sum_nonneg fun x _ => le_min (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  linarith

/-- If `P(x) = Q(x) ρ(x)` for every `x`, then `d_TV(P, Q) = ∑ₓ Q(x) max (1 - ρ(x), 0)`.
No positivity of `Q` or of `ρ` is assumed. -/
theorem tvDist_eq_sum_mul_max {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (ρ : α → ℝ)
    (hρ : ∀ x, (P {x} : ℝ) = (Q {x} : ℝ) * ρ x) :
    tvDist P Q = ∑ x, (Q {x} : ℝ) * max (1 - ρ x) 0 := by
  have key : ∀ x, |(P {x} : ℝ) - (Q {x} : ℝ)| =
      ((P {x} : ℝ) - (Q {x} : ℝ)) + 2 * ((Q {x} : ℝ) * max (1 - ρ x) 0) := by
    intro x
    have hq : (0 : ℝ) ≤ (Q {x} : ℝ) := NNReal.coe_nonneg _
    rw [hρ x, show (Q {x} : ℝ) * ρ x - (Q {x} : ℝ) = (Q {x} : ℝ) * (ρ x - 1) by ring,
      abs_mul, abs_of_nonneg hq]
    rcases le_total (ρ x) 1 with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
      ring
  unfold tvDist
  rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_coe_apply_singleton, sum_coe_apply_singleton, ← Finset.mul_sum]
  ring

end Parking
