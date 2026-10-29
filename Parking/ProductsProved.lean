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

public import Parking.External
import Parking.MainTheorem
import Parking.Products
import Parking.ProxyTV

/-!
# Consequences of the proof of `AKVZ26.ProductTV`

The hypothesis `AKVZ26.ProductTV` is proved in `Parking.ProxyTV`
(`akvz26_productTV`). This module discharges it in the results that assumed it:

* `tvDist_marginalProduct_comparable`: `lem:products`, now without hypothesis;
* `tvDist_firstCoordsLaw_bounds_of_BH20`: the conclusion of `thm:main`, now conditional on
  `BH20.SupportGenFunCLC` only.
-/

public section

namespace Parking

/-- `lem:products`: there are constants `0 < c, C` such that, for all
`n ≥ 2` and `1 ≤ k ≤ n`, `d_TV(μ_n^{⊗k}, Q_{n,k})` lies between `c min (1, √b)` and
`C min (1, √b)`, with `b = k log (k + 1) / n`. -/
theorem tvDist_marginalProduct_comparable :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → k ≤ n →
      c * min 1 √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ)) ≤
          tvDist (marginalProduct n k) (uniformProduct n k) ∧
        tvDist (marginalProduct n k) (uniformProduct n k) ≤
          C * min 1 √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ)) :=
  tvDist_marginalProduct_comparable_of_AKVZ26 akvz26_productTV

/-- `thm:main`, conditional on `BH20.SupportGenFunCLC` only: the conclusion of
`tvDist_firstCoordsLaw_bounds_of_BH20_AKVZ26`, with `AKVZ26.ProductTV` discharged by `akvz26_productTV`. -/
theorem tvDist_firstCoordsLaw_bounds_of_BH20 (hBH : BH20.SupportGenFunCLC) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → ∀ hkn : k ≤ n,
        √((k : ℝ) * Real.log ((k : ℝ) + 1) /
            (C * (n : ℝ) + (k : ℝ) * Real.log ((k : ℝ) + 1)))
          ≤ tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ∧
        tvDist (firstCoordsLaw n k hkn) (uniformProduct n k)
          ≤ min 1 (C * √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ))) :=
  tvDist_firstCoordsLaw_bounds_of_BH20_AKVZ26 hBH akvz26_productTV

end Parking

end
