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

public import Parking.ProxyMarginal

/-!
# `lem:products`, conditional on `AKVZ26.ProductTV`

This module proves `lem:products` from the general product-TV comparison,

`d_TV(μ_n^{⊗k}, Q_{n,k}) ≍ min (1, √(k log (k + 1) / n))` for `n ≥ 2` and `1 ≤ k ≤ n`,

with constants independent of `n` and `k`, under the external hypothesis `AKVZ26.ProductTV`
(`AKVZ26.ProductTV`, defined in `Parking.External`), which is an explicit hypothesis of
`tvDist_marginalProduct_comparable_of_AKVZ26` and is never asserted.

The proof applies `AKVZ26.ProductTV` to the finite set `Fin n`, the laws `P = μ_n` and `Q = U_n`, and the scale
`s = √b_{n,k}`, with `b_{n,k} = k log (k + 1) / n`. Its scalar premise `c₁ ≤ k Ψ(s) ≤ C₁` is
`exists_akvzProxy_marginal_comparable`. Its premise `μ_n ≠ U_n` follows from
`c₁ > 0`, since the proxy of a law against itself vanishes (`akvzProxy_self`). The products
`ProbabilityMeasure.pi fun _ : Fin k => μ_n` and `ProbabilityMeasure.pi fun _ : Fin k => U_n`
are `marginalProduct n k` and `uniformProduct n k` by definition.
-/

public section

namespace Parking

open MeasureTheory

/-- The AKVZ proxy of a law against itself vanishes: `Ψ(s) = 0` for `P = Q`, since the score
`(P(x) - P(x)) / (P(x) + P(x))` is `0` at every `x`. -/
theorem akvzProxy_self {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P : ProbabilityMeasure α) (s : ℝ) : akvzProxy P P s = 0 := by
  simp [akvzProxy, akvzScore]

/-- `lem:products`, conditional on `AKVZ26.ProductTV`. -/
theorem tvDist_marginalProduct_comparable_of_AKVZ26 (hAKVZ : AKVZ26.ProductTV) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → k ≤ n →
      c * min 1 √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ)) ≤
          tvDist (marginalProduct n k) (uniformProduct n k) ∧
        tvDist (marginalProduct n k) (uniformProduct n k) ≤
          C * min 1 √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ)) := by
  obtain ⟨c₁, C₁, h1, h2, h⟩ := exists_akvzProxy_marginal_comparable
  obtain ⟨c, C, hc, hC, hH⟩ := hAKVZ c₁ C₁ h1 h2
  refine ⟨c, C, hc, hC, fun n hn k hk hkn => ?_⟩
  have hs : 0 < √(bScale n k) := Real.sqrt_pos.2 (bScale_pos n.pos hk)
  have hne : marginal n ≠ uniformLaw (Fin n) := by
    intro heq
    have := (h n hn k hk hkn).1
    rw [heq, akvzProxy_self] at this
    linarith
  exact hH (Fin n) (marginal n) (uniformLaw (Fin n)) hne k hk _ hs
    (h n hn k hk hkn).1 (h n hn k hk hkn).2

end Parking

end
