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
import Parking.DecouplingBound
import Parking.SupportGenFunCLC

/-!
# Provider for `prop:decoupling`

`Parking.Provider.klDiv_tvDist_firstCoordsLaw_le` proves the exported statement
`Parking.klDiv_tvDist_firstCoordsLaw_le` (`Parking/Frozen/Decoupling.lean`) from proved results
only: the conditional form `klDiv_tvDist_firstCoordsLaw_le_of_BH20` (`Parking.DecouplingBound`)
applied to the proof of `BH20.SupportGenFunCLC`, `bh20_supportGenFunCLC` (`Parking.SupportGenFunCLC`).

The statement is the exported theorem, except that its binders are implicit (the data, recovered from
the goal) or filled by `assumption` (the hypotheses). This lets the exported proof body be the
single assembly `by exact Parking.Provider.klDiv_tvDist_firstCoordsLaw_le`, inside the context
of the exported binders.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace Parking.Provider

/-- `prop:decoupling`, with the binders of the exported statement made
implicit or filled by `assumption`. -/
theorem klDiv_tvDist_firstCoordsLaw_le {n : ℕ+} (hn : 2 ≤ (n : ℕ) := by assumption) {k : ℕ}
    (hk : 1 ≤ k := by assumption) (hkn : k ≤ n := by assumption) :
    klDiv (firstCoordsLaw n k hkn : Measure (Fin k → Fin n))
        (marginalProduct n k : Measure (Fin k → Fin n))
      ≤ ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) *
          Real.log (n : ℝ)) ∧
    tvDist (firstCoordsLaw n k hkn) (marginalProduct n k)
      ≤ √((k : ℝ) * ((k : ℝ) - 1) * Real.log (n : ℝ) /
          (2 * (n : ℝ) * ((n : ℝ) - 1))) :=
  klDiv_tvDist_firstCoordsLaw_le_of_BH20 bh20_supportGenFunCLC n hn k hk hkn

end Parking.Provider

end
