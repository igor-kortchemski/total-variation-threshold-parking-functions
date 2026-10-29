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
public import Parking.MainScalarPaper
import Parking.Products
import Parking.Separation
import Parking.TVDist

/-!
# Assembly of the manuscript's main bounds

The proof follows `thm:main`. The approximation
error is bounded through the displayed logarithmic chain `eq:tv_decoupling`.
Its upper-bound use is `b log(e/b) ≤ 1`; its small-scale lower-bound use is
`b log(e/b) → 0`. Separation and the final common constant are assembled as
in the manuscript. The citation interfaces are discharged by the ordinary
proved interfaces used in the exported theorems.
-/

public section

namespace Parking

/-- The complete displayed chain `eq:tv_decoupling`, with absolute constant `2`.
Both inequalities are kept together and consumed by the main upper/lower proofs. -/
theorem tvDist_firstCoordsLaw_marginal_le_paper_chain (hBH : BH20.SupportGenFunCLC)
    (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hb : bScale n k < 1) :
    tvDist (firstCoordsLaw n k hkn) (marginalProduct n k) ≤
        (k : ℝ) / n * √(Real.log n) ∧
      (k : ℝ) / n * √(Real.log n) ≤
        2 * bScale n k * √(Real.log (Real.exp 1 / bScale n k)) :=
  ⟨(klDiv_tvDist_firstCoordsLaw_le_of_BH20 hBH n hn k hk hkn).2.trans
      (sqrt_decoupling_le_mul_sqrt_log hn hk hkn),
    mul_sqrt_log_le_two_bScale_sqrt_log hn hk hb⟩

/-- Upper bound in `thm:main`, conditional on `BH20.SupportGenFunCLC` and `AKVZ26.ProductTV`: there is `C ≥ 1` such that
`d_TV(P_{n,k}, Q_{n,k}) ≤ C √(k log (k + 1) / n)` for `n ≥ 2` and `1 ≤ k ≤ n`. -/
theorem exists_tvDist_firstCoordsLaw_le_of_BH20_AKVZ26 (hBH : BH20.SupportGenFunCLC)
    (hAKVZ : AKVZ26.ProductTV) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → ∀ hkn : k ≤ n,
      tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ≤
        C * √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ)) := by
  obtain ⟨_, Cp, _, hCp, hP⟩ := tvDist_marginalProduct_comparable_of_AKVZ26 hAKVZ
  refine ⟨Cp + 2, by linarith, fun n hn k hk hkn => ?_⟩
  have hb : (k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ) = bScale n k := rfl
  have hb0 : 0 < bScale n k := bScale_pos n.pos hk
  have hs0 : 0 ≤ √(bScale n k) := Real.sqrt_nonneg _
  rw [hb]
  rcases le_or_gt 1 (bScale n k) with h1 | h1
  · -- `b ≥ 1`: `d_TV ≤ 1 ≤ √b`.
    have hs1 : 1 ≤ √(bScale n k) := Real.one_le_sqrt.2 h1
    calc tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ≤ 1 := tvDist_le_one _ _
      _ ≤ √(bScale n k) := hs1
      _ ≤ (Cp + 2) * √(bScale n k) := by nlinarith
  · -- `b < 1`: triangle inequality through `μ_n^{⊗k}`.
    have hT1 : tvDist (firstCoordsLaw n k hkn) (marginalProduct n k) ≤ 2 * √(bScale n k) := by
      obtain ⟨hfirst, hsecond⟩ := tvDist_firstCoordsLaw_marginal_le_paper_chain hBH n hn k hk hkn h1
      refine hfirst.trans (hsecond.trans ?_)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (b_mul_sqrt_log_exp_div_le_sqrt hb0.le) (by norm_num : (0 : ℝ) ≤ 2)
    have hT2 : tvDist (marginalProduct n k) (uniformProduct n k) ≤ Cp * √(bScale n k) := by
      have h2 := (hP n hn k hk hkn).2
      rw [hb] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hCp.le)
    calc tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ≤
        tvDist (firstCoordsLaw n k hkn) (marginalProduct n k) +
          tvDist (marginalProduct n k) (uniformProduct n k) := tvDist_triangle _ _ _
      _ ≤ 2 * √(bScale n k) + Cp * √(bScale n k) := add_le_add hT1 hT2
      _ = (Cp + 2) * √(bScale n k) := by ring

/-- Small-scale lower bound in `thm:main`, conditional on `BH20.SupportGenFunCLC` and `AKVZ26.ProductTV`: there are `b₀ ∈ (0, 1]` and `c > 0`
such that `d_TV(P_{n,k}, Q_{n,k}) ≥ c √b_{n,k}` for `n ≥ 2`, `1 ≤ k ≤ n` and
`b_{n,k} = k log (k + 1) / n ≤ b₀`. -/
theorem exists_le_tvDist_firstCoordsLaw_of_BH20_AKVZ26 (hBH : BH20.SupportGenFunCLC)
    (hAKVZ : AKVZ26.ProductTV) :
    ∃ b₀ c : ℝ, 0 < b₀ ∧ b₀ ≤ 1 ∧ 0 < c ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k →
      ∀ hkn : k ≤ n, (k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ) ≤ b₀ →
        c * √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ)) ≤
          tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) := by
  obtain ⟨cp, _, hcp, _, hP⟩ := tvDist_marginalProduct_comparable_of_AKVZ26 hAKVZ
  obtain ⟨b₀, hb₀, hb₀1, hsmall⟩ := exists_small_mul_log_exp_div
    (by positivity : (0 : ℝ) < cp ^ 2 / 16)
  refine ⟨b₀, cp / 2, hb₀, hb₀1.le, half_pos hcp, fun n hn k hk hkn hbnd => ?_⟩
  have hb : (k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ) = bScale n k := rfl
  have hb0 : 0 < bScale n k := bScale_pos n.pos hk
  rw [hb] at hbnd ⊢
  have hb1 : bScale n k < 1 := hbnd.trans_lt hb₀1
  have hs1 : √(bScale n k) ≤ 1 := Real.sqrt_le_one.2 hb1.le
  have hT2 : cp * √(bScale n k) ≤ tvDist (marginalProduct n k) (uniformProduct n k) := by
    have h2 := (hP n hn k hk hkn).1
    rw [hb, min_eq_right hs1] at h2
    exact h2
  have hsc : √(bScale n k * Real.log (Real.exp 1 / bScale n k)) ≤ cp / 4 := by
    apply (Real.sqrt_le_left (by positivity)).2
    have h := hsmall (bScale n k) hb0 hbnd
    nlinarith
  have hT1 : tvDist (firstCoordsLaw n k hkn) (marginalProduct n k) ≤ cp * √(bScale n k) / 2 := by
    obtain ⟨hfirst, hsecond⟩ := tvDist_firstCoordsLaw_marginal_le_paper_chain hBH n hn k hk hkn hb1
    refine hfirst.trans (hsecond.trans ?_)
    rw [mul_assoc, b_mul_sqrt_log_exp_div hb0.le]
    have h := mul_le_mul_of_nonneg_left hsc (Real.sqrt_nonneg (bScale n k))
    nlinarith
  have htri := tvDist_triangle (marginalProduct n k) (firstCoordsLaw n k hkn)
    (uniformProduct n k)
  rw [tvDist_comm (marginalProduct n k) (firstCoordsLaw n k hkn)] at htri
  linarith

/-- `thm:main` (`thm:main`, proved on `thm:main`), conditional
on `BH20.SupportGenFunCLC` and `AKVZ26.ProductTV`. The conclusion is that of
`thm:main`, with `hBH` and `hAKVZ` prepended: there is `C ≥ 1` such that, for `n ≥ 2` and
`1 ≤ k ≤ n`, with `b = k log (k + 1) / n`,
`√(b / (C + b)) ≤ d_TV(P_{n,k}, Q_{n,k}) ≤ min (1, C √b)`. -/
theorem tvDist_firstCoordsLaw_bounds_of_BH20_AKVZ26 (hBH : BH20.SupportGenFunCLC)
    (hAKVZ : AKVZ26.ProductTV) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → ∀ hkn : k ≤ n,
        √((k : ℝ) * Real.log ((k : ℝ) + 1) /
            (C * (n : ℝ) + (k : ℝ) * Real.log ((k : ℝ) + 1)))
          ≤ tvDist (firstCoordsLaw n k hkn) (uniformProduct n k) ∧
        tvDist (firstCoordsLaw n k hkn) (uniformProduct n k)
          ≤ min 1 (C * √((k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ))) := by
  obtain ⟨Cup, _, hup⟩ := exists_tvDist_firstCoordsLaw_le_of_BH20_AKVZ26 hBH hAKVZ
  obtain ⟨b₀, cs, hb₀, _, hcs, hlow⟩ := exists_le_tvDist_firstCoordsLaw_of_BH20_AKVZ26 hBH hAKVZ
  obtain ⟨c', hc', hsep⟩ := exists_one_sub_exp_bScale_le_tvDist_of_BH20 hBH
  obtain ⟨C, hC1, hCup, hCcs, hCc'⟩ : ∃ C : ℝ, 1 ≤ C ∧ Cup ≤ C ∧ 1 / cs ^ 2 ≤ C ∧
      2 / c' + 1 / (c' ^ 2 * b₀) ≤ C :=
    ⟨max (max 1 Cup) (max (1 / cs ^ 2) (2 / c' + 1 / (c' ^ 2 * b₀))),
      (le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  refine ⟨C, hC1, fun n hn k hk hkn => ⟨?_, ?_⟩⟩
  · have hb : (k : ℝ) * Real.log ((k : ℝ) + 1) / (n : ℝ) = bScale n k := rfl
    have hb0 : 0 < bScale n k := bScale_pos n.pos hk
    rw [div_add_eq_bScale n.pos (by linarith)]
    rcases le_total (bScale n k) b₀ with h | h
    · -- `b ≤ b₀`: the small-`b` lower bound.
      have h1 := hlow n hn k hk hkn (by rw [hb]; exact h)
      rw [hb] at h1
      exact (sqrt_div_add_le_mul_sqrt hcs hCcs hb0.le).trans h1
    · -- `b ≥ b₀`: `eq:separation`.
      have h2 := hsep n hn k hk hkn
      rw [hb] at h2
      exact (sqrt_div_add_le_one_sub_exp hc' hb₀ hCc' h).trans h2
  · refine le_min (tvDist_le_one _ _) ((hup n hn k hk hkn).trans ?_)
    exact mul_le_mul_of_nonneg_right hCup (Real.sqrt_nonneg _)

end Parking

end
