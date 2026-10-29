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
import Parking.ProductsProved
import Parking.SupportGenFunCLC

/-!
# Provider for `thm:main`

`Parking.Provider.tvDist_firstCoordsLaw_bounds` proves the exported statement
`Parking.tvDist_firstCoordsLaw_bounds` (`Parking/Frozen/MainBounds.lean`) from proved results only:
the form `tvDist_firstCoordsLaw_bounds_of_BH20` (`Parking.ProductsProved`, where `AKVZ26.ProductTV` is discharged
by `akvz26_productTV`) applied to the proof of `BH20.SupportGenFunCLC`, `bh20_supportGenFunCLC`
(`Parking.SupportGenFunCLC`).
-/

public section

namespace Parking.Provider

/-- `thm:main`, with the statement of the exported theorem. -/
theorem tvDist_firstCoordsLaw_bounds :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → ∀ hkn : k ≤ n,
        √((k : ℝ) * Real.log ((k : ℝ) + 1) /
            (C * (n : ℝ) + (k : ℝ) * Real.log ((k : ℝ) + 1)))
          ≤ tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ∧
        tvDist (firstCoordsLaw n k hkn) (uniformProduct n k)
          ≤ min 1 (C * √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ))) :=
  tvDist_firstCoordsLaw_bounds_of_BH20 bh20_supportGenFunCLC

end Parking.Provider

end
