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
public import Parking.SqrtSums
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Borel normalization and endpoint telescoping

The cited Borel normalization is proved from the exact first-coordinate counting
identity and reflection, with the Stirling ratio estimate. This proof uses no
pointwise marginal bound or parking limit theorem. The manuscript's marginal
argument then starts at the first endpoint, as in `lem:marginal`.
-/

public section

namespace Parking

open Finset Filter Topology

/-- The relative gap estimate, separately from the leading Stirling approximation.
The zero-based index `i` represents the source index `i + 1`. -/
theorem abs_parkingGap_div_borelWeight_sub_one_le {n i : ℕ}
    (h : 2 * (i + 1) ≤ n + 1) :
    |parkingGap n i / borelWeight (i + 1) - 1| ≤
      4 * ((i : ℝ) + 1) / ((n : ℝ) + 1) := by
  obtain ⟨he, hq, -, -, -, hlo, hhi, hsum, hab, ha⟩ := parkingGap_factor_bounds h
  have hb : (0 : ℝ) < (n - i : ℕ) := by exact_mod_cast (show 0 < n - i by omega)
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlow : 1 / (12 * ((n - i : ℕ) : ℝ)) ≤
      4 * ((i : ℝ) + 1) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) hN]
    nlinarith
  have hupp : 2 * ((n : ℝ) + 1) / ((n - i : ℕ) : ℝ) - 2 ≤
      4 * ((i : ℝ) + 1) / ((n : ℝ) + 1) := by
    rw [show 2 * ((n : ℝ) + 1) / ((n - i : ℕ) : ℝ) - 2 =
        2 * ((i : ℝ) + 1) / ((n - i : ℕ) : ℝ) by
      apply (sub_eq_iff_eq_add).2
      field_simp
      nlinarith]
    rw [div_le_div_iff₀ hb hN]
    nlinarith
  rw [he, mul_div_cancel_left₀ _ hq.ne', abs_le]
  constructor <;> linarith

/-- The additive form of the uniform relative approximation. -/
theorem abs_parkingGap_sub_borelWeight_le {n i : ℕ}
    (h : 2 * (i + 1) ≤ n + 1) :
    |parkingGap n i - borelWeight (i + 1)| ≤
      4 / ((n : ℝ) + 1) * (((i : ℝ) + 1) * borelWeight (i + 1)) := by
  have hq := borelWeight_pos (i + 1)
  have hrel := abs_parkingGap_div_borelWeight_sub_one_le h
  have heq : parkingGap n i - borelWeight (i + 1) =
      (parkingGap n i / borelWeight (i + 1) - 1) * borelWeight (i + 1) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hq]
  calc _ ≤ (4 * ((i : ℝ) + 1) / ((n : ℝ) + 1)) * borelWeight (i + 1) :=
      mul_le_mul_of_nonneg_right hrel hq.le
    _ = _ := by ring

/-- Weighted partial sums of the Borel probabilities are bounded uniformly. -/
theorem sum_weighted_borelWeight_le (j : ℕ) :
    ∑ i ∈ range j, ((i : ℝ) + 1) * borelWeight (i + 1) ≤ √((j : ℝ) + 1) := by
  have hS : (2 : ℝ) ≤ √(2 * Real.pi) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith [Real.two_le_pi]
  have hterm (i : ℕ) : ((i : ℝ) + 1) * borelWeight (i + 1) ≤
      (1 / 2) * (1 / √((i : ℝ) + 1)) := by
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hq := borelWeight_le (k := i + 1) (by omega)
    push_cast at hq
    calc _ ≤ ((i : ℝ) + 1) * (1 / (√(2 * Real.pi) * ((i : ℝ) + 1) * √((i : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hq hi.le
      _ = (1 / √(2 * Real.pi)) * (1 / √((i : ℝ) + 1)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (one_div_le_one_div_of_le (by norm_num) hS) (by positivity)
  have hsum : ∑ i ∈ range j, 1 / √((i : ℝ) + 1) ≤ 2 * √((j : ℝ) + 1) := by
    have heq := sum_Ico_add' (fun i : ℕ => 1 / √(i : ℝ)) 0 j 1
    simp only [Nat.cast_add, Nat.cast_one, zero_add] at heq
    rw [range_eq_Ico, heq]
    simpa only [Nat.cast_add, Nat.cast_one] using sum_inv_sqrt_le (j + 1)
  calc _ ≤ ∑ i ∈ range j, (1 / 2 : ℝ) * (1 / √((i : ℝ) + 1)) :=
      sum_le_sum fun i _ => hterm i
    _ = (1 / 2 : ℝ) * ∑ i ∈ range j, 1 / √((i : ℝ) + 1) := (mul_sum _ _ _).symm
    _ ≤ (1 / 2 : ℝ) * (2 * √((j : ℝ) + 1)) := by gcongr
    _ = _ := by ring

/-- Sum of the relative errors on the exact left-half range. -/
theorem abs_sum_parkingGap_sub_borelWeight_le {n j : ℕ} (hj : 2 * j ≤ n + 1) :
    |(∑ i ∈ range j, parkingGap n i) - (∑ i ∈ range j, borelWeight (i + 1))| ≤
      4 * √((j : ℝ) + 1) / ((n : ℝ) + 1) := by
  rw [← sum_sub_distrib]
  calc _ ≤ ∑ i ∈ range j, |parkingGap n i - borelWeight (i + 1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range j, 4 / ((n : ℝ) + 1) *
        (((i : ℝ) + 1) * borelWeight (i + 1)) := by
      refine sum_le_sum fun i hi => abs_parkingGap_sub_borelWeight_le ?_
      have := mem_range.1 hi
      omega
    _ = 4 / ((n : ℝ) + 1) * (∑ i ∈ range j, ((i : ℝ) + 1) * borelWeight (i + 1)) :=
      (mul_sum _ _ _).symm
    _ ≤ 4 / ((n : ℝ) + 1) * √((j : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left (sum_weighted_borelWeight_le j) (by positivity)
    _ = _ := by ring

/-- Endpoint telescoping before Borel normalization is applied. -/
theorem abs_parkingG_sub_one_sub_sum_borelWeight_le (n : ℕ+) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ) + 1) :
    |parkingG n j - (1 - ∑ i ∈ range (j : ℕ), borelWeight (i + 1))| ≤
      6 * √((j : ℝ) + 1) / ((n : ℝ) + 1) := by
  have ht := parkingG_eq_add_sum n ⟨0, n.pos⟩ j (show (0 : ℕ) ≤ j from Nat.zero_le _)
  rw [parkingG_zero, ← range_eq_Ico] at ht
  have he := abs_sum_parkingGap_sub_borelWeight_le hj
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hzero : ((n : ℝ) - 1) / ((n : ℝ) + 1) = 1 - 2 / ((n : ℝ) + 1) := by
    field_simp
    ring
  have hsplit : parkingG n j - (1 - ∑ i ∈ range (j : ℕ), borelWeight (i + 1)) =
      - (2 / ((n : ℝ) + 1)) - ((∑ i ∈ range (j : ℕ), parkingGap n i) -
        (∑ i ∈ range (j : ℕ), borelWeight (i + 1))) := by
    rw [hzero] at ht
    linarith
  have hs : (1 : ℝ) ≤ √((j : ℝ) + 1) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ (j : ℝ))]
  have htri := abs_sub (-(2 / ((n : ℝ) + 1)))
    ((∑ i ∈ range (j : ℕ), parkingGap n i) - (∑ i ∈ range (j : ℕ), borelWeight (i + 1)))
  rw [← hsplit, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 / ((n : ℝ) + 1))] at htri
  have hlast : 2 / ((n : ℝ) + 1) + 4 * √((j : ℝ) + 1) / ((n : ℝ) + 1) ≤
      6 * √((j : ℝ) + 1) / ((n : ℝ) + 1) := by
    rw [← add_div, div_le_div_iff₀ hN hN]
    nlinarith
  exact (htri.trans (add_le_add le_rfl he)).trans hlast

/-- A quantitative convergence estimate for the positive-index partial sums.
Only the exact even-size reflection is used to identify the limit. -/
theorem abs_sum_borelWeight_sub_one_le {m : ℕ} (hm : 1 ≤ m) :
    |(∑ i ∈ range m, borelWeight (i + 1)) - 1| ≤ 7 / √((m : ℝ) + 1) := by
  let n : ℕ+ := ⟨2 * m, by omega⟩
  let j : Fin n := ⟨m, by dsimp [n]; omega⟩
  have hr := parkingG_add_parkingG_of_add_eq n j.isLt j.isLt
    (show (j : ℕ) + (j : ℕ) = (n : ℕ) by simp [n, j]; omega)
  have he := abs_parkingG_sub_one_sub_sum_borelWeight_le n j
    (show 2 * (j : ℕ) ≤ (n : ℕ) + 1 by simp [n, j])
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmid : parkingG n j = -(1 / ((n : ℝ) + 1)) := by
    change parkingG n j + parkingG n j = -2 / ((n : ℝ) + 1) at hr
    linear_combination hr / 2
  have hsum : |(∑ i ∈ range m, borelWeight (i + 1)) - 1| ≤
      7 * √((m : ℝ) + 1) / ((n : ℝ) + 1) := by
    have hs : (1 : ℝ) ≤ √((m : ℝ) + 1) := by
      rw [Real.le_sqrt' (by norm_num)]
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hdiff : (∑ i ∈ range m, borelWeight (i + 1)) - 1 =
        (parkingG n j - (1 - ∑ i ∈ range (j : ℕ), borelWeight (i + 1))) - parkingG n j := by
      simp only [j]
      ring
    calc _ ≤ |parkingG n j - (1 - ∑ i ∈ range (j : ℕ), borelWeight (i + 1))| +
        |parkingG n j| := by rw [hdiff]; exact abs_sub _ _
      _ ≤ 6 * √((m : ℝ) + 1) / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
        have habs : |parkingG n j| = 1 / ((n : ℝ) + 1) := by
          rw [hmid, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1 / ((n : ℝ) + 1))]
        rw [habs]
        exact add_le_add (by simpa only [j] using he) le_rfl
      _ ≤ _ := by
        rw [← add_div, div_le_div_iff₀ hN hN]
        nlinarith
  refine hsum.trans ?_
  have hs0 : (0 : ℝ) < √((m : ℝ) + 1) := by positivity
  rw [div_le_div_iff₀ hN hs0]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)
  change 7 * √((m : ℝ) + 1) * √((m : ℝ) + 1) ≤ 7 * ((2 * m : ℕ) + 1 : ℝ)
  push_cast
  nlinarith only [hs, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- Borel probabilities on positive indices have total mass one (DH17, §2.1).
The unused formula value at index zero is deliberately excluded. -/
theorem hasSum_borelWeight_succ : HasSum (fun i => borelWeight (i + 1)) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun i => (borelWeight_pos (i + 1)).le) 1).2
  apply tendsto_sub_nhds_zero_iff.1
  have hlim : Tendsto (fun m : ℕ => 7 / √((m : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with m hm
  simpa only [Real.norm_eq_abs] using abs_sum_borelWeight_sub_one_le hm

/-- The Borel tail equals one minus its preceding partial sum. -/
theorem tsum_borelWeight_add_eq_one_sub (j : ℕ) :
    (∑' i, borelWeight (i + j + 1)) = 1 - ∑ i ∈ range j, borelWeight (i + 1) := by
  exact ((hasSum_nat_add_iff' j).2 hasSum_borelWeight_succ).tsum_eq

/-- The first asymptotic display in the manuscript: telescope from `g_n(1)`
and compare with the infinite Borel tail, with an absolute uniform constant. -/
theorem abs_parkingG_sub_borelTail_le (n : ℕ+) (j : Fin n)
    (hj : 2 * (j : ℕ) ≤ (n : ℕ) + 1) :
    |parkingG n j - ∑' i, borelWeight (i + (j : ℕ) + 1)| ≤
      6 * √((j : ℝ) + 1) / ((n : ℝ) + 1) := by
  rw [tsum_borelWeight_add_eq_one_sub]
  exact abs_parkingG_sub_one_sub_sum_borelWeight_le n j hj

end Parking
