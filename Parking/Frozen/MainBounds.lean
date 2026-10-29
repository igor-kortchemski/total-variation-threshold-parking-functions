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
public import Parking.Provider.MainBounds

/-!
# Frozen statement: `thm:main`

Author-approved statement of `thm:main` (`parking_threshold.tex`, lines 89–100),
registered in `frozen-anchors.json` with state `SEALED`.
This export successor preserves the approved statement.
Its proof is the single assembly `by exact Parking.Provider.tvDist_firstCoordsLaw_bounds`.
Only `Solution.lean` may import this file in the approved export.
-/

public section

namespace Parking

/-- Theorem `thm:main` (source lines 89–100). -/
theorem tvDist_firstCoordsLaw_bounds :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → ∀ hkn : k ≤ n,
        √((k : ℝ) * Real.log ((k : ℝ) + 1) /
            (C * (n : ℝ) + (k : ℝ) * Real.log ((k : ℝ) + 1)))
          ≤ tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ∧
        tvDist (firstCoordsLaw n k hkn) (uniformProduct n k)
          ≤ min 1 (C * √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact Parking.Provider.tvDist_firstCoordsLaw_bounds
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end Parking

end
-- FROZEN_ANCHOR_SUFFIX_END
