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

public import Parking.Marginal
public import Parking.TVDist
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The log-likelihood ratio of `μ_n^{⊗k}` with respect to `Q_{n,k}`

This module follows the first part of the proof of `thm:profile`. Under `Q_{n,k} = U_n^{⊗k}` the coordinates `V_1, …, V_k` are independent and
uniform on `[n]`, and since `μ_n(j) = (1 + g_n(j)) / n`, the density of `μ_n^{⊗k}` with
respect to `Q_{n,k}` is `e^{L_{n,k}}`, where `L_{n,k} = ∑_r log (1 + g_n(V_r))` is the
log-likelihood ratio. Its law under `Q_{n,k}` is `Parking.llrLaw n k`.

* `marginalProduct_apply_singleton_eq_mul_exp`: `μ_n^{⊗k}(x) = Q_{n,k}(x) e^{L(x)}`, with
  `L(x) = ∑_r log (1 + g_n(x_r))`. All the factors `1 + g_n(j)` are positive since `μ_n`
  charges every point.
* `tvDist_marginalProduct_eq_integral`: `d_TV(μ_n^{⊗k}, Q_{n,k}) = E[(1 - e^{L_{n,k}})_+]`,
  from `Parking.tvDist_eq_sum_mul_max` and a finite-sum computation of the integral.
* `charFun_llrLaw`: the characteristic function of `L_{n,k}` is
  `u ↦ ((1/n) ∑ⱼ (1 + g_n(j))^{iu})^k`, where `(1 + g)^{iu} = exp (iu log (1 + g))`. The
  integral against the product measure factorizes into the `k`-th power of a one-coordinate
  integral.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Parking

/-- The law of the log-likelihood ratio `L_{n,k} = ∑_r log(1 + g_n(V_r))` under
`Q_{n,k} = U_n^{⊗k}` (`thm:profile`). -/
@[expose] noncomputable def llrLaw (n : ℕ+) (k : ℕ) : ProbabilityMeasure ℝ :=
  (uniformProduct n k).map fun x => ∑ r, Real.log (1 + parkingG n (x r))

/-- `1 + g_n(j) > 0`, since `μ_n(j) = (1 + g_n(j)) / n` and `μ_n` charges every point. -/
theorem one_add_parkingG_pos (n : ℕ+) (j : Fin n) : 0 < 1 + parkingG n j := by
  have h := marginal_apply_singleton_pos n j
  rw [marginal_apply_singleton_eq] at h
  exact (div_pos_iff_of_pos_right (Nat.cast_pos.2 n.pos)).1 h

/-- The density of `μ_n^{⊗k}` with respect to `Q_{n,k}` is `e^{L}`:
`μ_n^{⊗k}(x) = Q_{n,k}(x) exp (∑_r log (1 + g_n(x_r)))` (`thm:profile`). -/
theorem marginalProduct_apply_singleton_eq_mul_exp (n : ℕ+) (k : ℕ) (x : Fin k → Fin n) :
    (marginalProduct n k {x} : ℝ) =
      (uniformProduct n k {x} : ℝ) * Real.exp (∑ r, Real.log (1 + parkingG n (x r))) := by
  have h (r : Fin k) : Real.exp (Real.log (1 + parkingG n (x r))) = 1 + parkingG n (x r) :=
    Real.exp_log (one_add_parkingG_pos n (x r))
  rw [marginalProduct_apply_singleton, uniformProduct_apply_singleton, Real.exp_sum]
  simp_rw [h, marginal_apply_singleton_eq, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

/-- `d_TV(μ_n^{⊗k}, Q_{n,k}) = E[(1 - e^{L_{n,k}})_+]`, the expectation being taken under the
law `llrLaw n k` of `L_{n,k}` (`thm:profile`). -/
theorem tvDist_marginalProduct_eq_integral (n : ℕ+) (k : ℕ) :
    tvDist (marginalProduct n k) (uniformProduct n k) =
      ∫ y, max (1 - Real.exp y) 0 ∂(llrLaw n k : Measure ℝ) := by
  have hc : Continuous fun y : ℝ => max (1 - Real.exp y) 0 :=
    (continuous_const.sub Real.continuous_exp).max continuous_const
  rw [tvDist_eq_sum_mul_max _ _ _ (marginalProduct_apply_singleton_eq_mul_exp n k), llrLaw,
    ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_of_finite _).aemeasurable hc.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn, smul_eq_mul]

/-- The characteristic function of `L_{n,k}` is `u ↦ ((1/n) ∑ⱼ (1 + g_n(j))^{iu})^k`, where
`(1 + g)^{iu} = exp (iu log (1 + g))` (`thm:profile`). -/
theorem charFun_llrLaw (n : ℕ+) (k : ℕ) (u : ℝ) :
    charFun (llrLaw n k : Measure ℝ) u =
      ((∑ j : Fin n, Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I)) / n) ^ k := by
  have hc : Continuous fun y : ℝ => Complex.exp (u * y * Complex.I) := by fun_prop
  rw [charFun_apply_real, llrLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_of_finite _).aemeasurable hc.aestronglyMeasurable]
  have h (x : Fin k → Fin n) :
      Complex.exp (u * ((∑ r, Real.log (1 + parkingG n (x r)) : ℝ) : ℂ) * Complex.I) =
        ∏ r, Complex.exp (u * Real.log (1 + parkingG n (x r)) * Complex.I) := by
    rw [← Complex.exp_sum]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  have hpow := integral_fintype_prod_eq_pow (ι := Fin k)
    (fun j : Fin n => Complex.exp (u * Real.log (1 + parkingG n j) * Complex.I))
    (μ := (uniformLaw (Fin n) : Measure (Fin n)))
  beta_reduce at hpow
  simp_rw [h]
  rw [uniformProduct, ProbabilityMeasure.toMeasure_pi, hpow, Fintype.card_fin,
    integral_fintype Integrable.of_finite, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (uniformLaw (Fin n) : Measure (Fin n)).real {j} = 1 / n := by
    rw [ProbabilityMeasure.measureReal_eq_coe_coeFn]
    simpa using uniformLaw_apply ({j} : Finset (Fin n))
  rw [hj, Complex.real_smul]
  push_cast
  ring

end Parking
