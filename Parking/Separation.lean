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
public import Parking.Marginal
import Parking.MainScalar
import Parking.MarginalSquares
import Parking.ProductMoments
import Parking.TVDist

/-!
# The affinity bound and the separation inequality, conditional on `BH20.SupportGenFunCLC`

This module proves the affinity estimate and `eq:separation`. Write `P_{n,k}` for the law of the first `k` coordinates of a uniform parking
function of size `n`, `Q_{n,k} = U_n^{⊗k}`, `g_j = g_n(j)` (`Parking.parkingG`) and
`A = (1/n) ∑ⱼ √(1 + gⱼ)`. The module proves, conditional on the external hypothesis `BH20.SupportGenFunCLC`
(`BH20.SupportGenFunCLC`, defined in `Parking.External`), which is an explicit hypothesis of
each theorem and is never asserted:

* `one_sub_tvDist_le_pow_of_BH20` (Affinity estimate): `1 - d_TV(P_{n,k}, Q_{n,k}) ≤ A^k`.
  With `h(x) = ∏_r √(1 + g(x_r))`, the elementary bound `min_le_add_div_two` gives
  `min (P(x), Q(x)) ≤ (P(x) / h(x) + Q(x) h(x)) / 2`. The sum of `P(x) / h(x)` is a value of
  the count-generating polynomial at `zⱼ = (1 + gⱼ)^{-1/2}`, bounded by `A^k` through the
  product-moment inequality `eq:product_moments` (`eval_countPoly_firstCoordsLaw_le`, where
  `BH20.SupportGenFunCLC` is used). The sum of `Q(x) h(x)` equals `A^k` by the product structure of `Q_{n,k}`.
* `exists_one_sub_exp_le_tvDist_of_BH20` (`eq:separation`):
  `d_TV(P_{n,k}, Q_{n,k}) ≥ 1 - exp (-c k log n / n)` for `n ≥ 2` and `1 ≤ k ≤ n`, from
  `A ≤ exp (-(1 - A))`, `1 - A ≥ ∑ⱼ gⱼ² / (2 n (1 + √2)²)` (`sum_sq_div_le_one_sub_mean_sqrt`)
  and `∑ⱼ gⱼ² ≥ c log n` (`exists_sum_sq_parkingG_comparable`).
* `exists_one_sub_exp_bScale_le_tvDist_of_BH20` (Large-scale lower bound in `thm:main`, first inequality):
  `d_TV(P_{n,k}, Q_{n,k}) ≥ 1 - exp (-c b_{n,k})` with `b_{n,k} = k log (k + 1) / n`, since
  `log (k + 1) ≤ 2 log n`.
-/

public section

open MeasureTheory

namespace Parking

/-- The full AM–GM chain in the proof of `thm:main`, for positive `h`. -/
theorem min_le_sqrt_mul_and_sqrt_mul_le {p q h : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hh : 0 < h) :
    min p q ≤ √(p * q) ∧ √(p * q) ≤ (p / h + q * h) / 2 := by
  have ha0 : 0 ≤ p / h := div_nonneg hp hh.le
  have hb0 : 0 ≤ q * h := mul_nonneg hq hh.le
  have hab : p * q = p / h * (q * h) := by field_simp
  have hm0 : 0 ≤ min p q := le_min hp hq
  have hm2 : min p q * min p q ≤ p * q :=
    mul_le_mul (min_le_left _ _) (min_le_right _ _) hm0 hp
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith
  · apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [sq_nonneg (p / h - q * h)]

/-- The pointwise bound used in the affinity proof, now explicitly consuming both
parts of the displayed AM–GM chain. -/
theorem min_le_add_div_two {p q h : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hh : 0 < h) :
    min p q ≤ (p / h + q * h) / 2 := by
  obtain ⟨hfirst, hsecond⟩ := min_le_sqrt_mul_and_sqrt_mul_le hp hq hh
  exact hfirst.trans hsecond

/-- Affinity estimate (`thm:main`), conditional on `BH20.SupportGenFunCLC`: for `1 ≤ k ≤ n`,
`1 - d_TV(P_{n,k}, Q_{n,k}) ≤ ((1/n) ∑ⱼ √(1 + g_n(j)))^k`. -/
theorem one_sub_tvDist_le_pow_of_BH20 (hBH : BH20.SupportGenFunCLC) (n : ℕ+) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    1 - tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ≤
      ((∑ j, √(1 + parkingG n j)) / n) ^ k := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 n.pos
  have hg (j : Fin n) : 0 < 1 + parkingG n j := by
    have h := marginal_apply_singleton_pos n j
    rw [marginal_apply_singleton_eq] at h
    exact (div_pos_iff_of_pos_right hn0).1 h
  have hs0 (j : Fin n) : 0 < √(1 + parkingG n j) := Real.sqrt_pos.2 (hg j)
  have hh0 (x : Fin k → Fin n) : 0 < ∏ r, √(1 + parkingG n (x r)) :=
    Finset.prod_pos fun r _ => hs0 (x r)
  -- First sum: `E_P[1 / h] ≤ A^k`, by the product moments with `zⱼ = (1 + gⱼ)^{-1/2}`.
  have h1 : ∑ x, (firstCoordsLaw n k hkn {x} : ℝ) / ∏ r, √(1 + parkingG n (x r)) ≤
      ((∑ j, √(1 + parkingG n j)) / n) ^ k := by
    have hpm := eval_countPoly_firstCoordsLaw_le hBH n k hk hkn
      (fun j => (√(1 + parkingG n j))⁻¹) fun j => inv_pos.2 (hs0 j)
    rw [eval_countPoly] at hpm
    have hl : ∑ x, (firstCoordsLaw n k hkn {x} : ℝ) / ∏ r, √(1 + parkingG n (x r)) =
        ∑ x, (firstCoordsLaw n k hkn : Measure (Fin k → Fin n)).real {x} *
          ∏ r, (√(1 + parkingG n (x r)))⁻¹ := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [ProbabilityMeasure.measureReal_eq_coe_coeFn, Finset.prod_inv_distrib, div_eq_mul_inv]
    have hr : ∑ j, (marginal n {j} : ℝ) * (√(1 + parkingG n j))⁻¹ =
        (∑ j, √(1 + parkingG n j)) / n := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsq : 1 + parkingG n j = √(1 + parkingG n j) * √(1 + parkingG n j) :=
        (Real.mul_self_sqrt (hg j).le).symm
      have hne := (hs0 j).ne'
      rw [marginal_apply_singleton_eq]
      nth_rewrite 1 [hsq]
      field_simp
    rw [hl]
    rw [hr] at hpm
    exact hpm
  -- Second sum: `E_Q[h] = A^k`, by the product structure of `Q_{n,k}`.
  have h2 : ∑ x, (uniformProduct n k {x} : ℝ) * ∏ r, √(1 + parkingG n (x r)) =
      ((∑ j, √(1 + parkingG n j)) / n) ^ k := by
    simp only [uniformProduct_apply_singleton]
    rw [← Finset.mul_sum, div_pow, Fintype.sum_pow]
    ring
  rw [tvDist_eq_one_sub_sum_min]
  calc 1 - (1 - ∑ x, min (firstCoordsLaw n k hkn {x} : ℝ) (uniformProduct n k {x} : ℝ))
      = ∑ x, min (firstCoordsLaw n k hkn {x} : ℝ) (uniformProduct n k {x} : ℝ) := by ring
    _ ≤ ∑ x, ((firstCoordsLaw n k hkn {x} : ℝ) / ∏ r, √(1 + parkingG n (x r)) +
          (uniformProduct n k {x} : ℝ) * ∏ r, √(1 + parkingG n (x r))) / 2 :=
        Finset.sum_le_sum fun x _ =>
          min_le_add_div_two (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) (hh0 x)
    _ = ((∑ x, (firstCoordsLaw n k hkn {x} : ℝ) / ∏ r, √(1 + parkingG n (x r))) +
          ∑ x, (uniformProduct n k {x} : ℝ) * ∏ r, √(1 + parkingG n (x r))) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ ((∑ j, √(1 + parkingG n j)) / n) ^ k := by
        rw [h2]
        linarith

/-- `eq:separation` (`thm:main`), conditional on `BH20.SupportGenFunCLC`: there is `c > 0` such that, for `n ≥ 2` and `1 ≤ k ≤ n`,
`d_TV(P_{n,k}, Q_{n,k}) ≥ 1 - exp (-c k log n / n)`. The constant is
`c = c_m / (2 (1 + √2)²)`, where `∑ⱼ g_n(j)² ≥ c_m log n`. -/
theorem exists_one_sub_exp_le_tvDist_of_BH20 (hBH : BH20.SupportGenFunCLC) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → ∀ hkn : k ≤ n,
      1 - Real.exp (-(c * ((k : ℝ) * Real.log (n : ℝ) / (n : ℝ)))) ≤
        tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) := by
  obtain ⟨cm, _, hcm, _, hS⟩ := exists_sum_sq_parkingG_comparable
  refine ⟨cm / (2 * (1 + √2) ^ 2), by positivity, fun n hn k hk hkn => ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 n.pos
  have hA0 : 0 ≤ (∑ j, √(1 + parkingG n j)) / n :=
    div_nonneg (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _) hn0.le
  -- `1 - A ≥ c log n / n`.
  have hδ : cm / (2 * (1 + √2) ^ 2) * (Real.log n / n) ≤
      1 - (∑ j, √(1 + parkingG n j)) / n := by
    have h1 := sum_sq_div_le_one_sub_mean_sqrt (parkingG n) (sum_parkingG n) fun j =>
      ⟨by linarith [exp_neg_one_le_one_add_parkingG n hn j, Real.exp_pos (-1)],
        one_add_parkingG_le_two n j⟩
    have h2 := (hS n hn).1
    calc cm / (2 * (1 + √2) ^ 2) * (Real.log n / n) =
        cm * Real.log n / (2 * n * (1 + √2) ^ 2) := by
          field_simp
      _ ≤ (∑ j, parkingG n j ^ 2) / (2 * n * (1 + √2) ^ 2) := by gcongr
      _ ≤ 1 - (∑ j, √(1 + parkingG n j)) / n := h1
  -- `A ≤ exp (-(1 - A)) ≤ exp (-c log n / n)`.
  have hAexp : (∑ j, √(1 + parkingG n j)) / n ≤
      Real.exp (-(cm / (2 * (1 + √2) ^ 2) * (Real.log n / n))) := by
    calc (∑ j, √(1 + parkingG n j)) / n =
        -(1 - (∑ j, √(1 + parkingG n j)) / n) + 1 := by ring
      _ ≤ Real.exp (-(1 - (∑ j, √(1 + parkingG n j)) / n)) := Real.add_one_le_exp _
      _ ≤ Real.exp (-(cm / (2 * (1 + √2) ^ 2) * (Real.log n / n))) :=
          Real.exp_le_exp.2 (by linarith)
  have hpow := pow_le_pow_left₀ hA0 hAexp k
  rw [← Real.exp_nat_mul] at hpow
  have heq : (k : ℝ) * -(cm / (2 * (1 + √2) ^ 2) * (Real.log n / n)) =
      -(cm / (2 * (1 + √2) ^ 2) * ((k : ℝ) * Real.log (n : ℝ) / (n : ℝ))) := by
    ring
  rw [heq] at hpow
  linarith [one_sub_tvDist_le_pow_of_BH20 hBH n k hk hkn]

/-- Large-scale lower bound in `thm:main`, first inequality (`thm:main`),
conditional on `BH20.SupportGenFunCLC`: there is `c > 0` such that, for `n ≥ 2` and
`1 ≤ k ≤ n`, `d_TV(P_{n,k}, Q_{n,k}) ≥ 1 - exp (-c b_{n,k})`, with
`b_{n,k} = k log (k + 1) / n`. It follows from `eq:separation` and `log (k + 1) ≤ 2 log n`,
with half the constant. -/
theorem exists_one_sub_exp_bScale_le_tvDist_of_BH20 (hBH : BH20.SupportGenFunCLC) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → ∀ hkn : k ≤ n,
      1 - Real.exp (-(c * ((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ)))) ≤
        tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) := by
  obtain ⟨c, hc, h⟩ := exists_one_sub_exp_le_tvDist_of_BH20 hBH
  refine ⟨c / 2, half_pos hc, fun n hn k hk hkn => ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 n.pos
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog := log_add_one_le_two_mul_log hn hkn
  have hdiv : (k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ) ≤
      2 * ((k : ℝ) * Real.log (n : ℝ) / (n : ℝ)) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hn0]
    nlinarith
  have hle : c / 2 * ((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ)) ≤
      c * ((k : ℝ) * Real.log (n : ℝ) / (n : ℝ)) := by
    calc c / 2 * ((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ)) ≤
        c / 2 * (2 * ((k : ℝ) * Real.log (n : ℝ) / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = c * ((k : ℝ) * Real.log (n : ℝ) / (n : ℝ)) := by ring
  have hexp := Real.exp_le_exp.2 (neg_le_neg hle)
  linarith [h n hn k hk hkn]

end Parking

end
