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

public import Parking.Occupation
public import Parking.ProductMoments
public import Parking.SupportGenFunCLC

/-!
# The manuscript's joint occupation log-concavity lemma

The complete statement of `lem:occupation_logconcavity`, including its universal
product-moment conclusion and the source range `n ≥ 2`. The two proved interfaces
are assembled here with the support-generating-function provider discharged.
-/

public section

open MeasureTheory MvPolynomial

namespace Parking

/-- `lem:occupation_logconcavity`: the occupation polynomial is strongly
log-concave, and all initial segments satisfy the product-moment inequality. -/
theorem occupation_logconcavity (n : ℕ+) (_hn : 2 ≤ (n : ℕ)) :
    StronglyLogConcave (countPoly (parkingWordLaw n)) ∧
      ∀ (k : ℕ) (_hk1 : 1 ≤ k) (hk : k ≤ n) (z : Fin n → ℝ), (∀ j, 0 < z j) →
        eval z (countPoly (firstCoordsLaw n k hk : Measure (Fin k → Fin n))) ≤
          (∑ j, (marginal n {j} : ℝ) * z j) ^ k :=
  ⟨stronglyLogConcave_countPoly_parkingWordLaw bh20_supportGenFunCLC n,
    fun k hk1 hk z hz => eval_countPoly_firstCoordsLaw_le bh20_supportGenFunCLC n k hk1 hk z hz⟩

end Parking

end
