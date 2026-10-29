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

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Parking.External
public import Parking.Law
public import Parking.WordLaw
import Parking.EntropyKL
import Parking.Occupation
import Parking.Pinsker
import Parking.PrefixLaw
import Parking.SampleEntropy

/-!
# The decoupling bound, conditional on `BH20.SupportGenFunCLC`

`prop:decoupling`, proved
conditionally on the explicit hypothesis `BH20.SupportGenFunCLC`, which is never
asserted: for `n ≥ 2` and `1 ≤ k ≤ n`,
`KL(P_{n,k} ‖ μ_n^{⊗k}) ≤ k(k-1)/(n(n-1)) · log n` and
`d_TV(P_{n,k}, μ_n^{⊗k}) ≤ √(k(k-1) log n / (2n(n-1)))`.

* `coe_marginalProduct`: `μ_n^{⊗k}`, as a measure, is `Measure.pi`.
* `klDiv_parkingWordLaw_pi_le`: `KL(P_{n,n} ‖ μ_n^{⊗n}) ≤ log n` (`prop:decoupling`), stated for
  the law of the word `π_n`.
* `klDiv_firstCoordsLaw_le_of_BH20`: the relative entropy bound. It applies
  `klDiv_coordLaw_pi_le_of_stronglyLogConcave` (`lem:sample_entropy`) with `N = d = n`,
  `L` the law of `π_n` and `μ = μ_n`; strong log-concavity of the count-generating
  polynomial of `π_n` is `stronglyLogConcave_countPoly_parkingWordLaw`, the only use of `BH20.SupportGenFunCLC`.
* `klDiv_tvDist_firstCoordsLaw_le_of_BH20`: both bounds, the total variation bound following
  from Pinsker's inequality (`prop:decoupling`).
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace Parking

/-- `μ_n^{⊗k}`, as a measure, is the product measure `Measure.pi` of `k` copies of `μ_n`. -/
theorem coe_marginalProduct (n : ℕ+) (k : ℕ) :
    (marginalProduct n k : Measure (Fin k → Fin n)) =
      Measure.pi fun _ : Fin k => (marginal n : Measure (Fin n)) :=
  ProbabilityMeasure.toMeasure_pi _

/-- `prop:decoupling`: the law `L(π_n)` of the word
`(π_n(1), …, π_n(n))` satisfies `KL(L(π_n) ‖ μ_n^{⊗n}) ≤ log n`. -/
theorem klDiv_parkingWordLaw_pi_le (n : ℕ+) :
    klDiv (parkingWordLaw n) (Measure.pi fun _ : Fin n => (marginal n : Measure (Fin n))) ≤
      ENNReal.ofReal (Real.log (n : ℝ)) := by
  have h := klDiv_firstCoordsLaw_self_le n
  rwa [firstCoordsLaw_eq_coordLaw, coordLaw_self, coe_marginalProduct] at h

/-- The relative entropy bound of `prop:decoupling`, conditional on `BH20.SupportGenFunCLC`: for `n ≥ 2` and
`1 ≤ k ≤ n`, `KL(P_{n,k} ‖ μ_n^{⊗k}) ≤ k(k-1)/(n(n-1)) · log n`. -/
theorem klDiv_firstCoordsLaw_le_of_BH20 (hBH : BH20.SupportGenFunCLC) (n : ℕ+)
    (hn : 2 ≤ (n : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    klDiv (firstCoordsLaw n k hkn : Measure (Fin k → Fin n))
        (marginalProduct n k : Measure (Fin k → Fin n))
      ≤ ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) *
          Real.log (n : ℝ)) := by
  have : IsProbabilityMeasure (parkingWordLaw n) := by
    rw [parkingWordLaw]
    infer_instance
  have hμ (i : Fin n) : coordMarginalLaw (parkingWordLaw n) i = (marginal n : Measure (Fin n)) :=
    (marginal_eq_coordMarginalLaw n i).symm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
  rw [firstCoordsLaw_eq_coordLaw, coe_marginalProduct, ENNReal.ofReal_mul hc]
  calc klDiv (coordLaw (parkingWordLaw n) hkn)
        (Measure.pi fun _ : Fin k => (marginal n : Measure (Fin n)))
      ≤ ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))) *
          klDiv (parkingWordLaw n)
            (Measure.pi fun _ : Fin n => (marginal n : Measure (Fin n))) :=
        klDiv_coordLaw_pi_le_of_stronglyLogConcave hn (parkingWordLaw n)
          (isExchangeableLaw_parkingWordLaw n)
          (stronglyLogConcave_countPoly_parkingWordLaw hBH n) _ hμ hk hkn
    _ ≤ ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1))) *
          ENNReal.ofReal (Real.log (n : ℝ)) := by
        gcongr
        exact klDiv_parkingWordLaw_pi_le n

/-- `prop:decoupling`, conditional on
`BH20.SupportGenFunCLC`: for `n ≥ 2` and `1 ≤ k ≤ n`,
`KL(P_{n,k} ‖ μ_n^{⊗k}) ≤ k(k-1)/(n(n-1)) · log n` and
`d_TV(P_{n,k}, μ_n^{⊗k}) ≤ √(k(k-1) log n / (2n(n-1)))`. The second bound follows from the
first by Pinsker's inequality `2 d_TV² ≤ KL`. -/
theorem klDiv_tvDist_firstCoordsLaw_le_of_BH20 (hBH : BH20.SupportGenFunCLC) (n : ℕ+)
    (hn : 2 ≤ (n : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    klDiv (firstCoordsLaw n k hkn : Measure (Fin k → Fin n))
        (marginalProduct n k : Measure (Fin k → Fin n))
      ≤ ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) *
          Real.log (n : ℝ)) ∧
    tvDist (firstCoordsLaw n k hkn) (marginalProduct n k)
      ≤ √((k : ℝ) * ((k : ℝ) - 1) * Real.log (n : ℝ) /
          (2 * (n : ℝ) * ((n : ℝ) - 1))) := by
  have hKL := klDiv_firstCoordsLaw_le_of_BH20 hBH n hn k hk hkn
  refine ⟨hKL, Real.le_sqrt_of_sq_le ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hpin : 2 * tvDist (firstCoordsLaw n k hkn) (marginalProduct n k) ^ 2 ≤
      (k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) * Real.log (n : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc hlog)).1
      ((ofReal_two_mul_tvDist_sq_le_klDiv _ _).trans hKL)
  have heq : (k : ℝ) * ((k : ℝ) - 1) * Real.log (n : ℝ) / (2 * (n : ℝ) * ((n : ℝ) - 1)) =
      (k : ℝ) * ((k : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1)) * Real.log (n : ℝ) / 2 := by
    rw [div_mul_eq_mul_div, div_div, mul_comm ((n : ℝ) * ((n : ℝ) - 1)) 2, mul_assoc 2]
  rw [heq]
  linarith

end Parking

end
