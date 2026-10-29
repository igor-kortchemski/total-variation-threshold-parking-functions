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
public import Parking.MainScalarPaper
import Parking.ProductsProved
import Parking.ProfileTheorem
import Parking.Separation
import Parking.LlrLimit
import Parking.TVDist
import Parking.Pinsker
import Parking.SupportGenFunCLC

/-!
# The introductory threshold corollaries

The introductory threshold equivalence follows from the main upper estimate
and the separation estimate. These are downstream corollaries and do not enter
any proof of the main results. The final theorem modules are not imported here.
-/

public section

open Filter Topology

namespace Parking

/-- The uniform comparison stated in the abstract, with constants jointly chosen
before the positive size and the number of sampled coordinates. -/
theorem tvDist_firstCoordsLaw_comparable :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ,
      1 ≤ k → ∀ hkn : k ≤ n,
      c * min 1 √(bScale n k) ≤ tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ∧
      tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ≤ C * min 1 √(bScale n k) := by
  obtain ⟨C, hC, hmain⟩ := tvDist_firstCoordsLaw_bounds_of_BH20 bh20_supportGenFunCLC
  have hC0 : 0 < C := by linarith
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨1 / √(C + 1), C, by positivity, hC0, fun n hn k hk hkn => ?_⟩
  obtain ⟨hlow, hup⟩ := hmain n hn k hk hkn
  have hb : 0 < bScale n k := bScale_pos n.pos hk
  rw [div_add_eq_bScale n.pos hC0] at hlow
  change tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ≤
    min 1 (C * √(bScale n k)) at hup
  constructor
  · refine le_trans ?_ hlow
    rcases le_or_gt (bScale n k) 1 with hb1 | hb1
    · rw [min_eq_right (Real.sqrt_le_one.2 hb1)]
      calc 1 / √(C + 1) * √(bScale n k) = √(bScale n k / (C + 1)) := by
            rw [Real.sqrt_div hb.le]
            ring
        _ ≤ √(bScale n k / (C + bScale n k)) := by
            apply Real.sqrt_le_sqrt
            exact div_le_div_of_nonneg_left hb.le (by positivity) (by linarith)
    · rw [min_eq_left (Real.one_le_sqrt.2 hb1.le), mul_one]
      calc 1 / √(C + 1) = √(1 / (C + 1)) := by rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
        _ ≤ √(bScale n k / (C + bScale n k)) := by
            apply Real.sqrt_le_sqrt
            rw [div_le_div_iff₀ hC1 (by positivity)]
            nlinarith [mul_le_mul_of_nonneg_left hb1.le hC0.le]
  · rcases le_or_gt (√(bScale n k)) 1 with hs | hs
    · rw [min_eq_right hs]
      exact hup.trans (min_le_right _ _)
    · rw [min_eq_left hs.le, mul_one]
      exact (hup.trans (min_le_left _ _)).trans hC

/-- The introductory characterization: total variation tends to zero exactly when
`k_n log n/n → 0`, the precise positive-size formulation of `k_n = o(n/log n)`. -/
theorem tendsto_tvDist_firstCoordsLaw_zero_iff (k : ℕ+ → ℕ)
    (hk : ∀ n, 1 ≤ k n) (hkn : ∀ n, k n ≤ n) :
    Tendsto (fun n : ℕ+ => tvDist (firstCoordsLaw n (k n) (hkn n)) (uniformProduct n (k n)))
      atTop (𝓝 0) ↔
    Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro htv
    obtain ⟨c, hc, hsep⟩ := exists_one_sub_exp_le_tvDist_of_BH20 bh20_supportGenFunCLC
    have hgap : Tendsto (fun n : ℕ+ =>
        1 - Real.exp (-(c * ((k n : ℝ) * Real.log (n : ℝ) / (n : ℝ))))) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ htv
      · exact sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hc.le (kLogDiv_nonneg k n))))
      · filter_upwards [eventually_two_le_pnat] with n hn
        exact hsep n hn (k n) (hk n) (hkn n)
    have hexp : Tendsto (fun n : ℕ+ =>
        Real.exp (-(c * ((k n : ℝ) * Real.log (n : ℝ) / (n : ℝ))))) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ+ => (1 : ℝ)) atTop (𝓝 1)).sub hgap
      rw [sub_zero] at h
      exact h.congr (fun n => by ring)
    have hlog : Tendsto (fun n : ℕ+ =>
        -(c * ((k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_exp, Real.log_one] using
        (Real.continuousAt_log one_ne_zero).tendsto.comp hexp
    have h := hlog.div_const (-c)
    simpa only [neg_div_neg_eq, mul_div_cancel_left₀ _ hc.ne', zero_div] using h
  · intro hscale
    obtain ⟨C, hC, hmain⟩ := tvDist_firstCoordsLaw_bounds_of_BH20 bh20_supportGenFunCLC
    have hb : Tendsto (fun n : ℕ+ => bScale n (k n)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => (bScale_pos n.pos (hk n)).le) ?_
        (by simpa using hscale.const_mul 2)
      filter_upwards [eventually_two_le_pnat] with n hn
      have h := mul_le_mul_of_nonneg_left (log_add_one_le_two_mul_log hn (hkn n))
        (by positivity : (0 : ℝ) ≤ (k n : ℝ) / (n : ℝ))
      dsimp [bScale]
      convert h using 1 <;> ring
    have hbound : Tendsto (fun n : ℕ+ => C * √(bScale n (k n))) atTop (𝓝 0) := by
      simpa using hb.sqrt.const_mul C
    refine squeeze_zero' (Eventually.of_forall fun n => tvDist_nonneg _ _) ?_ hbound
    filter_upwards [eventually_two_le_pnat] with n hn
    exact (hmain n hn (k n) (hk n) (hkn n)).2.trans (min_le_right _ _)

/-- The same introductory equivalence in literal little-o notation. -/
theorem tendsto_tvDist_firstCoordsLaw_zero_iff_isLittleO (k : ℕ+ → ℕ)
    (hk : ∀ n, 1 ≤ k n) (hkn : ∀ n, k n ≤ n) :
    Tendsto (fun n : ℕ+ => tvDist (firstCoordsLaw n (k n) (hkn n)) (uniformProduct n (k n)))
      atTop (𝓝 0) ↔
    Asymptotics.IsLittleO atTop (fun n : ℕ+ => (k n : ℝ))
      (fun n : ℕ+ => (n : ℝ) / Real.log (n : ℝ)) := by
  have hne : ∀ᶠ n : ℕ+ in atTop, (n : ℝ) / Real.log (n : ℝ) = 0 → (k n : ℝ) = 0 := by
    filter_upwards [eventually_two_le_pnat] with n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : 0 < (n : ℝ) / Real.log (n : ℝ) := div_pos (by linarith) (Real.log_pos (by linarith))
    exact fun h => (hp.ne' h).elim
  rw [tendsto_tvDist_firstCoordsLaw_zero_iff k hk hkn, Asymptotics.isLittleO_iff_tendsto' hne]
  simp only [div_div_eq_mul_div]

/-- The above-threshold corollary stated in the introduction. -/
theorem tendsto_tvDist_firstCoordsLaw_one_of_kLogDiv_atTop (k : ℕ+ → ℕ)
    (hk : ∀ n, 1 ≤ k n) (hkn : ∀ n, k n ≤ n)
    (hlim : Tendsto (fun n : ℕ+ => (k n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) atTop atTop) :
    Tendsto (fun n : ℕ+ => tvDist (firstCoordsLaw n (k n) (hkn n)) (uniformProduct n (k n)))
      atTop (𝓝 1) :=
  tendsto_tvDist_firstCoordsLaw_one_of_BH20 bh20_supportGenFunCLC k hk hkn hlim

end Parking
