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

public import Parking.OccupationCounting
public import Parking.Paper.PrefixProduct
public import Parking.Paper.SupportNormalization

/-!
# Strong log-concavity of the parking occupation polynomial

The coefficient/counting infrastructure is reexported from `OccupationCounting`.
This module contains the concluding log-concavity interfaces.
-/

public section

open MeasureTheory MvPolynomial Finset

namespace Parking

/-- The prefix product is homogeneous of degree `n`, by its exact support
identification and the parking occupation degree constraint. -/
theorem isHomogeneous_prefixLinearProduct (n : ℕ+) :
    (prefixLinearProduct n).IsHomogeneous (n : ℕ) := by
  intro α hα
  have hmem : α ∈ parkingCountSet n := by
    rw [← support_prefixLinearProduct]
    exact mem_support_iff.mpr hα
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
    degree_of_mem_parkingCountSet hmem

/-- The manuscript's factorial support-normalization step, applied to the
strongly log-concave prefix product with exactly the parking count support. -/
theorem stronglyLogConcave_supportGenFun_parkingCountSet
    (hBH : BH20.SupportGenFunCLC) (n : ℕ+) :
    StronglyLogConcave (supportGenFun (parkingCountSet n)) := by
  have h := (stronglyLogConcave_prefixLinearProduct n).supportGenFun_of_BH20 hBH
    (isHomogeneous_prefixLinearProduct n)
  simpa only [support_prefixLinearProduct] using h

/-- The occupation polynomial is completely log-concave. Its proof follows the
source's prefix product, support normalization, and positive scalar identity;
the M-convex support is derived from strong log-concavity of the product. -/
theorem completelyLogConcave_countPoly_parkingWordLaw (hBH : BH20.SupportGenFunCLC) (n : ℕ+) :
    CompletelyLogConcave (countPoly (parkingWordLaw n)) := by
  rw [countPoly_parkingWordLaw]
  have hhom : (supportGenFun (parkingCountSet n)).IsHomogeneous (n : ℕ) :=
    isHomogeneous_supportGenFun
    (fun _ hα => degree_of_mem_parkingCountSet hα)
  exact ((stronglyLogConcave_supportGenFun_parkingCountSet hBH n).completelyLogConcave
    hhom).smul (by positivity)

/-- Strong log-concavity of the occupation polynomial, the first assertion of
`lem:occupation_logconcavity`. The citation parameter
is discharged by `bh20_supportGenFunCLC` at the ordinary downstream boundary. -/
theorem stronglyLogConcave_countPoly_parkingWordLaw (hBH : BH20.SupportGenFunCLC) (n : ℕ+) :
    StronglyLogConcave (countPoly (parkingWordLaw n)) :=
  (completelyLogConcave_countPoly_parkingWordLaw hBH n).stronglyLogConcave

end Parking

end
