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
import Parking.ProfileTheorem
import Parking.SupportGenFunCLC

/-!
# Provider for `thm:profile`

`Parking.Provider.tendsto_tvDist_firstCoordsLaw` proves the exported statement
`Parking.tendsto_tvDist_firstCoordsLaw` (`Parking/Frozen/Profile.lean`) from proved results only:
the conditional form `tendsto_tvDist_firstCoordsLaw_of_BH20` (`Parking.ProfileTheorem`) applied to
the proof of `BH20.SupportGenFunCLC`, `bh20_supportGenFunCLC` (`Parking.SupportGenFunCLC`).

The statement is the exported theorem, except that its binders are implicit (the data, recovered from
the goal) or filled by `assumption` (the hypotheses). This lets the exported proof body be the
single assembly `by exact Parking.Provider.tendsto_tvDist_firstCoordsLaw`, inside the context of
the exported binders.
-/

public section

open Filter Topology
open scoped ENNReal

namespace Parking.Provider

/-- `thm:profile`, with the binders of the exported statement made implicit
or filled by `assumption`. -/
theorem tendsto_tvDist_firstCoordsLaw {k : ℕ+ → ℕ} (hk : ∀ n, 1 ≤ k n := by assumption)
    (hkn : ∀ n, k n ≤ n := by assumption) {lam : ℝ≥0∞}
    (hlim : Tendsto (fun n : ℕ+ => ENNReal.ofReal ((k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 lam) := by assumption) :
    Tendsto (fun n : ℕ+ => tvDist (firstCoordsLaw n (k n) (hkn n)) (uniformProduct n (k n)))
      atTop (𝓝 (profile lam)) :=
  tendsto_tvDist_firstCoordsLaw_of_BH20 bh20_supportGenFunCLC k hk hkn lam hlim

end Parking.Provider

end
