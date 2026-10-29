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
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Parking.Law
public import Parking.Provider.Decoupling

/-!
# Frozen statement: `prop:decoupling`

Author-approved statement of `prop:decoupling` (`parking_threshold.tex`, lines 134–145),
registered in `frozen-anchors.json` with state `SEALED`.
This export successor preserves the approved statement.
Its proof is the single assembly `by exact Parking.Provider.klDiv_tvDist_firstCoordsLaw_le`.
Only `Solution.lean` may import this file in the approved export.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace Parking

/-- Proposition `prop:decoupling` (source lines 134–145). -/
theorem klDiv_tvDist_firstCoordsLaw_le (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    klDiv (firstCoordsLaw n k hkn : Measure (Fin k → Fin n))
        (marginalProduct n k : Measure (Fin k → Fin n))
      ≤ ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) *
          Real.log (n : ℝ)) ∧
    tvDist (firstCoordsLaw n k hkn) (marginalProduct n k)
      ≤ √((k : ℝ) * ((k : ℝ) - 1) * Real.log (n : ℝ) /
          (2 * (n : ℝ) * ((n : ℝ) - 1))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact Parking.Provider.klDiv_tvDist_firstCoordsLaw_le
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end Parking

end
-- FROZEN_ANCHOR_SUFFIX_END
