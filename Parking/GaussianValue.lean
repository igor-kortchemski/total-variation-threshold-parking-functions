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

/-!
# The Gaussian value of the limiting profile

The proof of `thm:profile` in the source paper
(`thm:profile`) uses, the Gaussian integral identity

`𝔼[(1 - exp (σ G - σ² / 2))₊] = 2 Φ(σ / 2) - 1`,  with `G ∼ N(0, 1)`,

where `Φ` is the standard normal distribution function, and then `σ² = 4λ/π`. Here the
law of `σ G - σ² / 2` is `N(-v/2, v)` with `v = σ²`. The identity is proved by
exponential tilting: `eʸ` times the density of `N(-v/2, v)` is the density of `N(v/2, v)`
(`exp_mul_gaussianPDFReal`), so that the expectation equals
`N(-v/2, v)((-∞, 0]) - N(v/2, v)((-∞, 0]) = Φ(√v / 2) - Φ(-√v / 2)`.

Main statements:

* `cdf_gaussianReal_neg`: `Φ(-x) = 1 - Φ(x)`;
* `gaussianReal_real_Iic`: `N(m, v)((-∞, x]) = Φ((x - m) / √v)` for `v ≠ 0`;
* `exp_mul_gaussianPDFReal`: the exponential tilting of the Gaussian density;
* `integral_max_one_sub_exp_gaussianReal`: `∫ (1 - eʸ)₊ dN(-v/2, v) = 2 Φ(√v / 2) - 1`;
* `integral_max_one_sub_exp_gaussianReal_eq_profile`: for `v = 4l/π`, this is
  `profile (ENNReal.ofReal l)`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Parking

/-! ### The standard normal distribution function -/

/-- Symmetry of the standard normal distribution function: `Φ(-x) = 1 - Φ(x)`. -/
theorem cdf_gaussianReal_neg (x : ℝ) :
    cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hneg : (gaussianReal 0 1).map (fun y ↦ -y) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have hpre : (fun y : ℝ ↦ -y) ⁻¹' Set.Iic (-x) = Set.Ici x := by
    ext y
    simp
  rw [cdf_eq_real, cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, Set.compl_Iic,
    measureReal_congr (Ioi_ae_eq_Ici (μ := gaussianReal 0 1) (a := x)), ← hpre,
    ← map_measureReal_apply (by fun_prop) measurableSet_Iic, hneg]

/-- The standard normal distribution function at `0`: `Φ(0) = 1/2`. -/
theorem cdf_gaussianReal_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have h := cdf_gaussianReal_neg 0
  rw [neg_zero] at h
  linarith

/-- Standardization: the image of `N(m, v)`, with `v ≠ 0`, by `y ↦ (y - m) / √v` is the
standard normal law. -/
theorem gaussianReal_map_standardize (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal m v).map (fun y ↦ (y - m) / √(v : ℝ)) = gaussianReal 0 1 := by
  have hcomp : (fun y ↦ (y - m) / √(v : ℝ)) = (fun y ↦ y / √(v : ℝ)) ∘ (fun y ↦ y - m) :=
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
    gaussianReal_map_div_const, sub_self, zero_div]
  congr 1
  ext
  simp [Real.sq_sqrt, hv]

/-- The distribution function of `N(m, v)`, with `v ≠ 0`, in terms of `Φ`:
`N(m, v)((-∞, x]) = Φ((x - m) / √v)`. -/
theorem gaussianReal_real_Iic (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal m v).real (Set.Iic x) = cdf (gaussianReal 0 1) ((x - m) / √(v : ℝ)) := by
  have hs : 0 < √(v : ℝ) := Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  rw [cdf_eq_real, ← gaussianReal_map_standardize m hv,
    map_measureReal_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext y
  simp only [Set.mem_Iic, Set.mem_preimage]
  rw [div_le_div_iff_of_pos_right hs, sub_le_sub_iff_right]

/-! ### Exponential tilting and the Gaussian value -/

/-- Exponential tilting of the Gaussian density: `eˣ` times the density of `N(-v/2, v)`
at `x` is the density of `N(v/2, v)` at `x`. -/
theorem exp_mul_gaussianPDFReal (v : ℝ≥0) (x : ℝ) :
    Real.exp x * gaussianPDFReal (-((v : ℝ) / 2)) v x = gaussianPDFReal ((v : ℝ) / 2) v x := by
  rcases eq_or_ne (v : ℝ) 0 with hv | hv
  · simp [gaussianPDFReal, hv]
  simp only [gaussianPDFReal]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- The mass of a set under a nondegenerate Gaussian law is the integral of the density
over this set. -/
theorem gaussianReal_real_eq_setIntegral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    (gaussianReal μ v).real s = ∫ x in s, gaussianPDFReal μ v x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral μ hv s,
    ENNReal.toReal_ofReal (integral_nonneg fun x ↦ gaussianPDFReal_nonneg μ v x)]

/-- The Gaussian value used in the proof of `thm:profile`: for `Y ∼ N(-v/2, v)`, that is
`Y = σ G - σ²/2` with `σ² = v`, one has `𝔼[(1 - e^Y)₊] = 2 Φ(√v / 2) - 1`. -/
theorem integral_max_one_sub_exp_gaussianReal (v : ℝ≥0) :
    ∫ y, max (1 - Real.exp y) 0 ∂(gaussianReal (-((v : ℝ) / 2)) v) =
      2 * cdf (gaussianReal 0 1) (√(v : ℝ) / 2) - 1 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [cdf_gaussianReal_zero]
  have hpt : (fun y ↦ gaussianPDFReal (-((v : ℝ) / 2)) v y • max (1 - Real.exp y) 0) =
      Set.indicator (Set.Iic 0)
        (fun y ↦ gaussianPDFReal (-((v : ℝ) / 2)) v y - gaussianPDFReal ((v : ℝ) / 2) v y) := by
    ext y
    rw [smul_eq_mul]
    by_cases hy : y ≤ 0
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy), ← exp_mul_gaussianPDFReal,
        max_eq_left (sub_nonneg.2 (Real.exp_le_one_iff.2 hy))]
      ring
    · rw [Set.indicator_of_notMem (by simpa using hy),
        max_eq_right (sub_nonpos.2 (Real.one_le_exp_iff.2 (le_of_not_ge hy))), mul_zero]
  have h1 : (0 - -((v : ℝ) / 2)) / √(v : ℝ) = √(v : ℝ) / 2 := by
    rw [zero_sub, neg_neg, div_right_comm, Real.div_sqrt]
  have h2 : (0 - (v : ℝ) / 2) / √(v : ℝ) = -(√(v : ℝ) / 2) := by
    rw [← h1, zero_sub, zero_sub, neg_neg, neg_div]
  rw [integral_gaussianReal_eq_integral_smul hv, hpt, integral_indicator measurableSet_Iic,
    integral_sub (integrable_gaussianPDFReal _ _).integrableOn
      (integrable_gaussianPDFReal _ _).integrableOn,
    ← gaussianReal_real_eq_setIntegral _ hv, ← gaussianReal_real_eq_setIntegral _ hv,
    gaussianReal_real_Iic _ hv, gaussianReal_real_Iic _ hv, h1, h2, cdf_gaussianReal_neg]
  ring

/-- Gaussian integral: with `σ² = 4l/π`, the Gaussian value
`𝔼[(1 - exp (σ G - σ² / 2))₊]` is `profile (ENNReal.ofReal l) = 2 Φ(√(l/π)) - 1`
(`thm:profile`). -/
theorem integral_max_one_sub_exp_gaussianReal_eq_profile {l : ℝ} (hl : 0 ≤ l) :
    ∫ y, max (1 - Real.exp y) 0 ∂(gaussianReal (-(2 * l / Real.pi)) (4 * l / Real.pi).toNNReal) =
      profile (ENNReal.ofReal l) := by
  have hv : ((4 * l / Real.pi).toNNReal : ℝ) = 4 * l / Real.pi :=
    Real.coe_toNNReal _ (by positivity)
  have hm : -(2 * l / Real.pi) = -(((4 * l / Real.pi).toNNReal : ℝ) / 2) := by
    rw [hv]
    ring
  have hsq : √(4 * l / Real.pi) / 2 = √(l / Real.pi) := by
    rw [show 4 * l / Real.pi = 2 ^ 2 * (l / Real.pi) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
    ring
  rw [hm, integral_max_one_sub_exp_gaussianReal, hv, hsq, profile,
    ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hl]

end Parking
