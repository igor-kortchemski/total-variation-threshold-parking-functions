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

public import Parking.ProductScore
import Parking.Symmetrization
import Parking.TVDist

/-!
# Total variation between product laws and the score norm

This module proves [AKVZ26, Theorem 1.1] for two laws `P`, `Q` on a finite set
and identical factors: the total variation `d_TV(P^{⊗k}, Q^{⊗k})` is comparable, with
universal constants, to `min(1, A)`, where `A = 𝔼 (∑_r U_r²)^{1/2}` is the score norm
`akvzScoreNorm P Q k`. The argument follows the proof of [AKVZ26, Theorem 1.1], with the explicit
threshold `ρ₀ = 1/100`.

Notation as in `Parking.ProductScore`: `M = (P + Q) / 2`, `u` the AKVZ score, `a = 𝔼_M u²`,
`ρ = k a`, `U_r = u(X_r)` for `X_1, …, X_k` independent of law `M`, `S = ∑ r, U_r`,
`Φ = (∏ r, (1 + U_r) - ∏ r, (1 - U_r)) / 2` and `R = Φ - S`. By step 1,
`d_TV(P^{⊗k}, Q^{⊗k}) = 𝔼 |Φ|`, so `𝔼 |S| - 𝔼 |R| ≤ d_TV ≤ 𝔼 |S| + 𝔼 |R|`
(`sum_mul_abs_le_add_sum_mul_abs_sub`).

* If `ρ ≤ 1/100`: `𝔼 |R| ≤ √(ρ³ / 5) ≤ ρ / 22` (step 2), `A ≥ 1 - e^{-ρ/2} ≥ ρ / 3`
  (step 3) and `𝔼 |S| ≥ A / (2√3) ≥ 2 A / 7` (step 4, `marcinkiewiczZygmund_one`). Hence
  `𝔼 |R| ≤ 𝔼 |S| / 2`, and `A / 7 ≤ d_TV ≤ 3 A`.
* If `ρ > 1/100`: by step 3, both `d_TV` and `A` are at least `1 - e^{-1/200} ≥ 1/201`.

The explicit result is `tvDist_pi_comparable_scoreNorm`:
`min(1, A) / 201 ≤ d_TV(P^{⊗k}, Q^{⊗k}) ≤ 201 min(1, A)`, for every `k`, including `k = 0`.
The existential form is `exists_tvDist_pi_comparable_scoreNorm`.
-/

public section

open MeasureTheory

namespace Parking

/-! ### Elementary inequalities -/

/-- `t / (1 + t) ≤ 1 - e^{-t}` for `t ≥ 0`, a rearrangement of `1 + t ≤ e^t`. -/
theorem div_one_add_le_one_sub_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    t / (1 + t) ≤ 1 - Real.exp (-t) := by
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp (-t) * (1 + t) ≤ 1 := by
    calc Real.exp (-t) * (1 + t) ≤ Real.exp (-t) * Real.exp t :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 1 := h2
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **Triangle inequalities for weighted absolute moments**: for nonnegative weights `W`,
`∑ W |f| ≤ ∑ W |g| + ∑ W |f - g|` and `∑ W |g| ≤ ∑ W |f| + ∑ W |f - g|`. -/
theorem sum_mul_abs_le_add_sum_mul_abs_sub {ι : Type*} (t : Finset ι) (W f g : ι → ℝ)
    (hW : ∀ i, 0 ≤ W i) :
    ∑ i ∈ t, W i * |f i| ≤ ∑ i ∈ t, W i * |g i| + ∑ i ∈ t, W i * |f i - g i| ∧
      ∑ i ∈ t, W i * |g i| ≤ ∑ i ∈ t, W i * |f i| + ∑ i ∈ t, W i * |f i - g i| := by
  constructor
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith [abs_sub_abs_le_abs_sub (f i) (g i)]) (hW i)
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_add]
    have h := abs_sub_abs_le_abs_sub (g i) (f i)
    rw [abs_sub_comm (g i) (f i)] at h
    exact mul_le_mul_of_nonneg_left (by linarith) (hW i)

/-! ### Step 5 of the proof of [AKVZ26, Theorem 1.1] -/

/-- **[AKVZ26, Theorem 1.1], explicit constants**, for finite alphabets and identical
factors (with `ρ₀ = 1/100`): with `A = akvzScoreNorm P Q k`,
`min(1, A) / 201 ≤ d_TV(P^{⊗k}, Q^{⊗k}) ≤ 201 min(1, A)`. -/
theorem tvDist_pi_comparable_scoreNorm {α : Type} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : ProbabilityMeasure α) (k : ℕ) :
    1 / 201 * min 1 (akvzScoreNorm P Q k) ≤
        tvDist (ProbabilityMeasure.pi fun _ : Fin k => P)
          (ProbabilityMeasure.pi fun _ : Fin k => Q) ∧
      tvDist (ProbabilityMeasure.pi fun _ : Fin k => P)
          (ProbabilityMeasure.pi fun _ : Fin k => Q) ≤ 201 * min 1 (akvzScoreNorm P Q k) := by
  have hA0 : 0 ≤ akvzScoreNorm P Q k := akvzScoreNorm_nonneg P Q k
  have hTV1 := tvDist_le_one (ProbabilityMeasure.pi fun _ : Fin k => P)
    (ProbabilityMeasure.pi fun _ : Fin k => Q)
  have hρ0 : 0 ≤ (k : ℝ) * akvzVar P Q := mul_nonneg (Nat.cast_nonneg k) (akvzVar_nonneg P Q)
  have hexpTV := one_sub_exp_le_tvDist_pi P Q k
  have hexpA := one_sub_exp_le_akvzScoreNorm P Q k
  have hexp := div_one_add_le_one_sub_exp_neg (t := (k : ℝ) * akvzVar P Q / 2) (by positivity)
  rw [neg_div] at hexpTV hexpA
  have hmin1 := min_le_left 1 (akvzScoreNorm P Q k)
  have hminA := min_le_right 1 (akvzScoreNorm P Q k)
  rcases le_or_gt ((k : ℝ) * akvzVar P Q) (1 / 100) with hsmall | hlarge
  · -- Small `ρ`: the linear part `S` dominates the remainder `R`.
    obtain ⟨hMZ, hMZ2⟩ := marcinkiewiczZygmund_one (akvzMid P Q) (akvzScore P Q)
      (akvzMid_nonneg P Q) (sum_akvzMid P Q) (sum_akvzMid_mul_akvzScore P Q) k
    have hAdef : akvzScoreNorm P Q k = ∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) *
        √(∑ r, akvzScore P Q (x r) ^ 2) := rfl
    rw [← hAdef] at hMZ hMZ2
    have hER := sum_abs_remainder_le P Q k (by linarith)
    have htri := sum_mul_abs_le_add_sum_mul_abs_sub Finset.univ (fun x : Fin k → α =>
      ∏ r, akvzMid P Q (x r))
      (fun x => (∏ r, (1 + akvzScore P Q (x r)) - ∏ r, (1 - akvzScore P Q (x r))) / 2)
      (fun x => ∑ r, akvzScore P Q (x r)) (prod_akvzMid_nonneg P Q)
    beta_reduce at htri
    rw [← tvDist_pi_eq_sum_oddPart] at htri
    obtain ⟨htri1, htri2⟩ := htri
    set TV := tvDist (ProbabilityMeasure.pi fun _ : Fin k => P)
      (ProbabilityMeasure.pi fun _ : Fin k => Q)
    set A := akvzScoreNorm P Q k
    set ρ := (k : ℝ) * akvzVar P Q
    set ES := ∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) * |∑ r, akvzScore P Q (x r)|
    set ER := ∑ x : Fin k → α, (∏ r, akvzMid P Q (x r)) *
      |(∏ r, (1 + akvzScore P Q (x r)) - ∏ r, (1 - akvzScore P Q (x r))) / 2 -
        ∑ r, akvzScore P Q (x r)|
    -- `√3 ≤ 7 / 4`, hence `2 A / 7 ≤ 𝔼 |S|`.
    have hs3 : √3 ≤ 7 / 4 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have hs3pos : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
    have hc : 2 / 7 ≤ 1 / (2 * √3) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hES : 2 / 7 * A ≤ ES := (mul_le_mul_of_nonneg_right hc hA0).trans hMZ
    -- `ρ / 3 ≤ A`.
    have hAρ : ρ / 3 ≤ A := by
      refine le_trans ?_ (hexp.trans hexpA)
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    -- `𝔼 |R| ≤ ρ / 22`.
    have hERρ : ER ≤ ρ / 22 := by
      refine hER.trans (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩)
      nlinarith [mul_nonneg (sq_nonneg ρ) (by linarith : (0 : ℝ) ≤ 5 / 484 - ρ)]
    have hRS : ER ≤ ES / 2 := by linarith
    constructor
    · calc 1 / 201 * min 1 A ≤ A / 7 := by linarith
        _ ≤ ES / 2 := by linarith
        _ ≤ TV := by linarith
    · rcases le_total 1 A with h | h
      · rw [min_eq_left h]
        linarith
      · rw [min_eq_right h]
        linarith
  · -- Large `ρ`: both `d_TV` and `A` are at least `1/201`.
    have h201 : 1 / 201 ≤ 1 - Real.exp (-((k : ℝ) * akvzVar P Q / 2)) := by
      refine le_trans ?_ hexp
      rw [le_div_iff₀ (by positivity)]
      linarith
    constructor
    · linarith
    · have : 1 / 201 ≤ min 1 (akvzScoreNorm P Q k) := le_min (by norm_num) (by linarith)
      linarith

/-- **[AKVZ26, Theorem 1.1]** for finite alphabets and identical factors: there are universal constants `c, C > 0` such that
`c min(1, A) ≤ d_TV(P^{⊗k}, Q^{⊗k}) ≤ C min(1, A)` for all laws `P`, `Q` on a finite set and
all `k`, where `A = akvzScoreNorm P Q k`. One can take `c = 1/201` and `C = 201`
(`tvDist_pi_comparable_scoreNorm`). -/
theorem exists_tvDist_pi_comparable_scoreNorm : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (α : Type) [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
      (P Q : ProbabilityMeasure α) (k : ℕ),
      c * min 1 (akvzScoreNorm P Q k) ≤
          tvDist (ProbabilityMeasure.pi fun _ : Fin k => P)
            (ProbabilityMeasure.pi fun _ : Fin k => Q) ∧
        tvDist (ProbabilityMeasure.pi fun _ : Fin k => P)
            (ProbabilityMeasure.pi fun _ : Fin k => Q) ≤ C * min 1 (akvzScoreNorm P Q k) :=
  ⟨1 / 201, 201, by norm_num, by norm_num, fun _ _ _ _ P Q k =>
    tvDist_pi_comparable_scoreNorm P Q k⟩

end Parking

end
