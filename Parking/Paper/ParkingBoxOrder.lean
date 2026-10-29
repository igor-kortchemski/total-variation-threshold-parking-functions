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

public import Parking.Paper.ParkingBoxes
public import Parking.Paper.PitmanStanleyMinkowski
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Parking boxes and ordered coordinates

Positive points belong to a parking box precisely when their sorted coordinates
lie below the cumulative parameter cuts. This is the geometric counterpart of
the manuscript's sorted parking-function characterization.
-/

public section

open Finset

namespace Parking

/-- Within a cumulative interval, threshold comparisons are exactly bin-index comparisons. -/
theorem parking_interval_cut_iff (n : ℕ+) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    {x : ℝ} {a j : Fin n}
    (hx : x ∈ Set.Ioc (∑ k ∈ Iio a, z k) (∑ k ∈ Iic a, z k)) :
    x ≤ ∑ k ∈ Iic j, z k ↔ a ≤ j := by
  constructor
  · intro h
    by_contra hnot
    have hja : j < a := lt_of_not_ge hnot
    have hc : ∑ k ∈ Iic j, z k ≤ ∑ k ∈ Iio a, z k :=
      sum_le_sum_of_subset_of_nonneg
        (fun k hk => mem_Iio.mpr ((mem_Iic.mp hk).trans_lt hja)) (fun k _ _ => hz k)
    exact (h.trans hc).not_gt hx.1
  · intro haj
    exact hx.2.trans (sum_le_sum_of_subset_of_nonneg (Iic_subset_Iic.mpr haj)
      (fun k _ _ => hz k))

/-- Every positive point below the total mass belongs to a cumulative interval,
even when some parameter intervals have zero length. -/
theorem exists_parking_interval (n : ℕ+) (z : Fin n → ℝ)
    {x : ℝ} (hx : 0 < x) (hxt : x ≤ ∑ i, z i) :
    ∃ a : Fin n, x ∈ Set.Ioc (∑ k ∈ Iio a, z k) (∑ k ∈ Iic a, z k) := by
  have hn := n.pos
  have hex : ∃ k : ℕ, k < (n : ℕ) ∧ x ≤ prefixMass n z (k + 1) := by
    refine ⟨(n : ℕ) - 1, by omega, ?_⟩
    simpa only [Nat.sub_add_cancel hn, prefixMass_total] using hxt
  let k := Nat.find hex
  have hk : k < (n : ℕ) ∧ x ≤ prefixMass n z (k + 1) := Nat.find_spec hex
  refine ⟨⟨k, hk.1⟩, ?_, ?_⟩
  · rw [← prefixMass_Iio]
    change prefixMass n z k < x
    by_cases hk0 : k = 0
    · simpa only [hk0, prefixMass_zero] using hx
    · by_contra hnot
      have hprev : k - 1 < (n : ℕ) ∧ x ≤ prefixMass n z (k - 1 + 1) := by
        refine ⟨by omega, ?_⟩
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using le_of_not_gt hnot
      have hmin := Nat.find_min' hex hprev
      change k ≤ k - 1 at hmin
      omega
  · rw [← prefixMass_Iic]
    exact hk.2

/-- Reindexing a finite vector preserves every threshold count. -/
theorem card_real_le_comp_perm {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (t : ℝ) :
    #{i | x (σ i) ≤ t} = #{i | x i ≤ t} := by
  apply card_equiv σ
  intro i
  simp

/-- The exact sorted-coordinate characterization of the geometric box union. -/
theorem mem_parkingBoxUnion_iff_sorted (n : ℕ+) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (x : Fin n → ℝ) :
    x ∈ parkingBoxUnion n z ↔
      (∀ i, 0 < x i) ∧ ∀ i, x (Tuple.sort x i) ≤ ∑ j ∈ Iic i, z j := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp h
    have hx (i : Fin n) := ha i (Set.mem_univ i)
    refine ⟨fun i => (sum_nonneg (fun j _ => hz j)).trans_lt (hx i).1, fun j => ?_⟩
    apply (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort x)).mp
    simp only [Function.comp_apply]
    rw [card_real_le_comp_perm]
    have hcount : #{i | x i ≤ ∑ k ∈ Iic j, z k} = #{i | a.val i ≤ j} := by
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and, parking_interval_cut_iff n z hz (hx i)]
    rw [hcount]
    exact Nat.lt_of_succ_le (a.property j)
  · rintro ⟨hx, hsort⟩
    have hn := n.pos
    let last : Fin n := ⟨(n : ℕ) - 1, by omega⟩
    have hlast : Iic last = univ := by
      ext i
      simp only [mem_Iic, mem_univ, iff_true]
      change i.val ≤ (n : ℕ) - 1
      have hi := i.isLt
      omega
    have htop : ∀ i, x i ≤ ∑ j, z j := by
      intro i
      have hi : (Tuple.sort x).symm i ≤ last := by
        change ((Tuple.sort x).symm i).val ≤ (n : ℕ) - 1
        have hi := ((Tuple.sort x).symm i).isLt
        omega
      have h := (Tuple.monotone_sort x hi).trans (hsort last)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, hlast] using h
    choose a ha using fun i => exists_parking_interval n z (hx i) (htop i)
    have hap : isParkingFunction a := by
      intro j
      have h := (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort x)).mpr (hsort j)
      simp only [Function.comp_apply] at h
      rw [card_real_le_comp_perm] at h
      have hcount : #{i | x i ≤ ∑ k ∈ Iic j, z k} = #{i | a i ≤ j} := by
        congr 1
        ext i
        simp only [mem_filter, mem_univ, true_and, parking_interval_cut_iff n z hz (ha i)]
      rw [hcount] at h
      exact Nat.succ_le_of_lt h
    apply Set.mem_iUnion.mpr
    refine ⟨⟨a, hap⟩, ?_⟩
    exact fun i _ => ha i

end Parking

end
