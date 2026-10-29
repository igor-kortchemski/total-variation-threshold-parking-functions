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
import Parking.DecouplingBound
import Parking.GaussianValue
import Parking.LikelihoodLaw
import Parking.LlrLimit
import Parking.MainScalarPaper
import Parking.Pinsker
import Parking.Separation
import Parking.TVDist

/-!
# `thm:profile`, conditional on `BH20.SupportGenFunCLC`

This module proves `thm:profile` under the
external hypothesis `BH20.SupportGenFunCLC` (`BH20.SupportGenFunCLC`, defined in `Parking.External`), which is an
explicit hypothesis of each theorem that uses it and is never asserted. No other citation interface is assumed.

Write `P = P_{n,k}`, `μ = μ_n^{⊗k}`, `Q = Q_{n,k}` and `x_n = k_n log n / n`.

* `tendsto_tvDist_marginalProduct` (Finite-parameter limit, no hypothesis): if `x_n → l`, then
  `d_TV(μ, Q) → F(l)`. By `Parking.LikelihoodLaw`, `d_TV(μ, Q) = E[(1 - e^{L_{n,k_n}})_+]`; by `Parking.LlrLimit`, the law of
  `L_{n,k_n}` converges weakly to `N(-2l/π, 4l/π)`, tested here against the bounded continuous
  function `y ↦ (1 - e^y)_+ ∈ [0, 1]`; `Parking.GaussianValue` computes the Gaussian value.
* `tendsto_tvDist_firstCoordsLaw_marginalProduct_of_BH20` (Reduction to the marginal product): if
  `x_n → l`, then `d_TV(P, μ) → 0`. By `prop:decoupling`,
  `d_TV(P, μ) ≤ (k_n/n) √(log n) → 0`, with the displayed scalar limit proved explicitly.
* `tendsto_tvDist_firstCoordsLaw_one_of_BH20` (Infinite-parameter limit): if `x_n → ∞`, then
  `d_TV(P, Q) → 1`, since `1 - e^{-c x_n} ≤ d_TV(P, Q) ≤ 1` by `eq:separation`.
* `tendsto_tvDist_firstCoordsLaw_of_BH20` (`thm:profile`): the binders and conclusion of the
  main statement, with `hBH` prepended. The hypothesis on `λ ∈ [0, ∞]` is split by
  `Parking.tendsto_ofReal_iff`; for finite `λ = l` the triangle inequality
  `|d_TV(P, Q) - d_TV(μ, Q)| ≤ d_TV(P, μ)` combines the first two limits.
-/

public section

open Filter Topology
open scoped ENNReal

namespace Parking

/-- Finite-parameter limit (`thm:profile`): if `k_n log n / n → l`,
then `d_TV(μ_n^{⊗k_n}, Q_{n,k_n}) → F(l) = 2Φ(√(l/π)) - 1`. The limit `l` is nonnegative
since every term of the sequence is. -/
theorem tendsto_tvDist_marginalProduct (k : ℕ+ → ℕ) (l : ℝ)
    (hl : Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ+ => tvDist (marginalProduct n (k n)) (uniformProduct n (k n))) atTop
      (𝓝 (profile (ENNReal.ofReal l))) := by
  have hl0 : 0 ≤ l := ge_of_tendsto' hl fun n => kLogDiv_nonneg k n
  have hc : Continuous fun y : ℝ => max (1 - Real.exp y) 0 :=
    (continuous_const.sub Real.continuous_exp).max continuous_const
  have hb : ∀ y : ℝ, ‖max (1 - Real.exp y) 0‖ ≤ 1 := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [Real.exp_pos y]) zero_le_one
  have h := MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    (tendsto_llrLaw k l hl) (BoundedContinuousFunction.ofNormedAddCommGroup _ hc 1 hb)
  rw [← integral_max_one_sub_exp_gaussianReal_eq_profile hl0]
  simp_rw [tvDist_marginalProduct_eq_integral]
  exact h

/-- The explicit scalar limit used in `thm:profile`: for finite profile parameter,
`(k_n/n) sqrt(log n) → 0`. -/
theorem tendsto_mul_sqrt_log_div_of_tendsto_kLogDiv {k : ℕ+ → ℕ} {l : ℝ}
    (hl : Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ+ => (k n : ℝ) / (n : ℝ) * √(Real.log (n : ℝ))) atTop (𝓝 0) := by
  have h := hl.div_atTop
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_pnat_cast_atTop))
  refine h.congr fun n => ?_
  calc (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ) / √(Real.log (n : ℝ)) =
      (k n : ℝ) / (n : ℝ) * (Real.log (n : ℝ) / √(Real.log (n : ℝ))) := by ring
    _ = (k n : ℝ) / (n : ℝ) * √(Real.log (n : ℝ)) := by rw [Real.div_sqrt]

/-- Reduction to the marginal product (`thm:profile`): the manuscript's explicit
`k_n sqrt(log n)/n` bound tends to zero, hence decoupling reduces the profile to products. -/
theorem tendsto_tvDist_firstCoordsLaw_marginalProduct_of_BH20 (hBH : BH20.SupportGenFunCLC)
    (k : ℕ+ → ℕ) (hk : ∀ n, 1 ≤ k n) (hkn : ∀ n, k n ≤ n) (l : ℝ)
    (hl : Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ+ => tvDist (firstCoordsLaw n (k n) (hkn n)) (marginalProduct n (k n)))
      atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun n => tvDist_nonneg _ _) ?_
    (tendsto_mul_sqrt_log_div_of_tendsto_kLogDiv hl)
  filter_upwards [eventually_two_le_pnat] with n hn
  exact (klDiv_tvDist_firstCoordsLaw_le_of_BH20 hBH n hn (k n) (hk n) (hkn n)).2.trans
    (sqrt_decoupling_le_mul_sqrt_log hn (hk n) (hkn n))

/-- Infinite-parameter limit (`thm:profile`), conditional on `BH20.SupportGenFunCLC`: if `k_n log n / n → ∞`, then `d_TV(P_{n,k_n}, Q_{n,k_n}) → 1`,
since `1 - exp (-c k_n log n / n) ≤ d_TV(P_{n,k_n}, Q_{n,k_n}) ≤ 1` by `eq:separation`. -/
theorem tendsto_tvDist_firstCoordsLaw_one_of_BH20 (hBH : BH20.SupportGenFunCLC)
    (k : ℕ+ → ℕ) (hk : ∀ n, 1 ≤ k n) (hkn : ∀ n, k n ≤ n)
    (hl : Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop atTop) :
    Tendsto (fun n : ℕ+ => tvDist (firstCoordsLaw n (k n) (hkn n)) (uniformProduct n (k n)))
      atTop (𝓝 1) := by
  obtain ⟨c, hc, hsep⟩ := exists_one_sub_exp_le_tvDist_of_BH20 hBH
  have hlow : Tendsto (fun n : ℕ+ =>
      1 - Real.exp (-(c * ((k n : ℝ) * Real.log (n : ℝ) / (n : ℝ))))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hl.const_mul_atTop hc))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun n => tvDist_le_one _ _)
  filter_upwards [eventually_two_le_pnat] with n hn
  exact hsep n hn (k n) (hk n) (hkn n)

/-- `thm:profile`, conditional on `BH20.SupportGenFunCLC`: the exported binders and
conclusion of `Parking.tendsto_tvDist_firstCoordsLaw`, copied verbatim, with `hBH`
prepended. -/
theorem tendsto_tvDist_firstCoordsLaw_of_BH20 (hBH : BH20.SupportGenFunCLC)
    (k : ℕ+ → ℕ) (hk : ∀ n, 1 ≤ k n)
    (hkn : ∀ n, k n ≤ n) (lam : ℝ≥0∞)
    (hlim : Tendsto (fun n : ℕ+ => ENNReal.ofReal ((k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 lam)) :
    Tendsto (fun n : ℕ+ => tvDist (firstCoordsLaw n (k n) (hkn n)) (uniformProduct n (k n)))
      atTop (𝓝 (profile lam)) := by
  rcases (tendsto_ofReal_iff (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      (kLogDiv_nonneg k) lam).1 hlim with ⟨rfl, h⟩ | ⟨l, -, rfl, h⟩
  · rw [show profile ∞ = 1 by simp [profile]]
    exact tendsto_tvDist_firstCoordsLaw_one_of_BH20 hBH k hk hkn h
  · have hdiff : Tendsto (fun n : ℕ+ =>
        tvDist (firstCoordsLaw n (k n) (hkn n)) (uniformProduct n (k n)) -
          tvDist (marginalProduct n (k n)) (uniformProduct n (k n))) atTop (𝓝 0) :=
      squeeze_zero_norm' (Eventually.of_forall fun n => by
          rw [Real.norm_eq_abs]
          exact abs_tvDist_sub_tvDist_le _ _ _)
        (tendsto_tvDist_firstCoordsLaw_marginalProduct_of_BH20 hBH k hk hkn l h)
    simpa only [sub_add_cancel, zero_add] using
      hdiff.add (tendsto_tvDist_marginalProduct k l h)

end Parking
