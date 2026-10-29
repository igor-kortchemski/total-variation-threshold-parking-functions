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
public import Parking.LogConcave

/-!
# Proved citation interfaces

The propositions `BH20.SupportGenFunCLC` and `AKVZ26.ProductTV` state the general
results of Brändén–Huh and Avital–Kontorovich–Vershynin–Zou used by the parking
proofs. Conditional lemmas expose these inputs explicitly. The final results
supply the proofs `bh20_supportGenFunCLC` from `Parking.SupportGenFunCLC` and
`akvz26_productTV` from `Parking.ProxyTV`.
-/

@[expose] public section

open MeasureTheory

namespace Parking

/-- The score `u(x) = (P(x) - Q(x)) / (P(x) + Q(x))`, equal to `0` where `P(x) + Q(x) = 0`
([AKVZ26, §1]; `lem:products`). -/
noncomputable def akvzScore {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : ProbabilityMeasure α) (x : α) : ℝ :=
  ((P {x} : ℝ) - Q {x}) / ((P {x} : ℝ) + Q {x})

/-- The proxy `Ψ(s) = ∑_x M(x) min(u(x)² / s², |u(x)| / s)`, with midpoint
`M = (P + Q) / 2` ([AKVZ26, (3.5)]; `lem:products`). -/
noncomputable def akvzProxy {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (s : ℝ) : ℝ :=
  ∑ x, ((P {x} : ℝ) + Q {x}) / 2 * min (akvzScore P Q x ^ 2 / s ^ 2) (|akvzScore P Q x| / s)

/-- **Support-generating-function interface.** [BH20, Theorem 3.10, (7) ⇒ (4)], then [BH20,
Theorem 2.30, (3) ⇒ (1)]: the generating function of a nonempty M-convex set of
exponents, all of total degree `m`, is completely log-concave. -/
def BH20.SupportGenFunCLC : Prop :=
  ∀ (d m : ℕ) (J : Finset (Fin d →₀ ℕ)), J.Nonempty → (∀ α ∈ J, α.degree = m) →
    IsMConvex (J : Set (Fin d →₀ ℕ)) → CompletelyLogConcave (supportGenFun J)

/-- **Product-TV comparison interface.** [AKVZ26, Section 3.3] for identical factors on a finite
set: for all `0 < c₁ ≤ C₁` there are `c, C > 0` such that, for all laws `P ≠ Q` on a finite
set, all `k ≥ 1` and all `s > 0` with `c₁ ≤ k Ψ(s) ≤ C₁`,
`c min(1, s) ≤ d_TV(P^{⊗k}, Q^{⊗k}) ≤ C min(1, s)`. It follows from [AKVZ26, Theorem 1.2]
with (3.4)–(3.6), or from [AKVZ26, Theorem 1.1] and an elementary comparison, without the
step of the proof of Theorem 1.2 that invokes Latała's theorem. The explicit dependence of
`c, C` on `c₁, C₁` is an elementary consequence that AKVZ26 does not state literally. The
premises `P ≠ Q` and `1 ≤ k` are implied by `c₁ ≤ k Ψ(s)` and kept for readability. -/
def AKVZ26.ProductTV : Prop :=
  ∀ c₁ C₁ : ℝ, 0 < c₁ → c₁ ≤ C₁ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (α : Type) [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
      (P Q : ProbabilityMeasure α), P ≠ Q → ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ, 0 < s →
        c₁ ≤ k * akvzProxy P Q s → k * akvzProxy P Q s ≤ C₁ →
          c * min 1 s ≤
              tvDist (ProbabilityMeasure.pi fun _ : Fin k => P)
                (ProbabilityMeasure.pi fun _ : Fin k => Q) ∧
            tvDist (ProbabilityMeasure.pi fun _ : Fin k => P)
                (ProbabilityMeasure.pi fun _ : Fin k => Q) ≤ C * min 1 s

end Parking

end
