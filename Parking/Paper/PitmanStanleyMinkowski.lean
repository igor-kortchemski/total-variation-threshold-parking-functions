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

public import Parking.Paper.PitmanStanley
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Constructive Minkowski decomposition of the Pitman–Stanley polytope

The transportation matrix consists of the lengths of intersections between
cumulative supply and demand intervals. Prefix domination forces the matrix to
be upper triangular. This proves the specialization of PS02 Theorem 9 used in
the manuscript, including zero parameters.
-/

@[expose] public section

open scoped BigOperators Pointwise

namespace Parking

noncomputable def prefixMass (n : ℕ+) (z : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), z i

theorem prefixMass_zero (n : ℕ+) (z : Fin n → ℝ) : prefixMass n z 0 = 0 := by
  simp [prefixMass]

theorem prefixMass_total (n : ℕ+) (z : Fin n → ℝ) : prefixMass n z n = ∑ i, z i := by
  simp [prefixMass]

theorem prefixMass_Iio (n : ℕ+) (z : Fin n → ℝ) (i : Fin n) :
    prefixMass n z i = ∑ j ∈ Finset.Iio i, z j := by
  unfold prefixMass
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]

theorem prefixMass_Iic (n : ℕ+) (z : Fin n → ℝ) (i : Fin n) :
    prefixMass n z (i.val + 1) = ∑ j ∈ Finset.Iic i, z j := by
  unfold prefixMass
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Fin.le_def, Nat.lt_succ_iff]

theorem prefixMass_step (n : ℕ+) (z : Fin n → ℝ) (i : Fin n) :
    prefixMass n z (i.val + 1) - prefixMass n z i = z i := by
  rw [prefixMass_Iic, prefixMass_Iio, ← Finset.Iio_insert,
    Finset.sum_insert (by simp)]
  ring

theorem prefixMass_mono (n : ℕ+) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    Monotone (prefixMass n z) := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans_le hij
  · exact fun k _ _ => hz k

theorem prefixMass_nonneg (n : ℕ+) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (k : ℕ) :
    0 ≤ prefixMass n z k :=
  Finset.sum_nonneg fun i _ => hz i

/-- Telescoping across all cumulative intervals. -/
theorem sum_prefixMass_diff (n : ℕ+) (z : Fin n → ℝ) (F : ℝ → ℝ) :
    (∑ i : Fin n, (F (prefixMass n z (i.val + 1)) - F (prefixMass n z i))) =
      F (∑ i, z i) - F 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => F (prefixMass n z (i + 1)) - F (prefixMass n z i))]
  rw [Finset.sum_range_sub (fun k => F (prefixMass n z k)) (n : ℕ),
    prefixMass_zero, prefixMass_total]

/-- The length of the intersection of cumulative supply interval `i` and demand interval `j`. -/
noncomputable def prefixTransport (n : ℕ+) (z y : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (min (prefixMass n z (i.val + 1)) (prefixMass n y (j.val + 1)) -
    min (prefixMass n z i) (prefixMass n y (j.val + 1))) -
  (min (prefixMass n z (i.val + 1)) (prefixMass n y j) -
    min (prefixMass n z i) (prefixMass n y j))

theorem prefixTransport_nonneg (n : ℕ+) (z y : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hy : ∀ j, 0 ≤ y j) (i j : Fin n) :
    0 ≤ prefixTransport n z y i j := by
  have hs := prefixMass_mono n z hz (Nat.le_succ i.val)
  have ht := prefixMass_mono n y hy (Nat.le_succ j.val)
  unfold prefixTransport
  simp only [min_def]
  split_ifs <;> linarith

theorem sum_prefixTransport_row_le (n : ℕ+) (z y : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (i : Fin n) :
    (∑ j, prefixTransport n z y i j) ≤ z i := by
  have hs := prefixMass_mono n z hz (Nat.le_succ i.val)
  have h0 := prefixMass_nonneg n z hz i
  have h1 := prefixMass_nonneg n z hz (i.val + 1)
  have h := sum_prefixMass_diff n y (fun t => min (prefixMass n z (i.val + 1)) t -
    min (prefixMass n z i) t)
  change (∑ j, prefixTransport n z y i j) = _ at h
  rw [h, min_eq_right h0, min_eq_right h1]
  have heq := prefixMass_step n z i
  simp only [min_def]
  split_ifs <;> linarith

theorem sum_prefixTransport_col (n : ℕ+) (z y : Fin n → ℝ)
    (hy : ∀ j, 0 ≤ y j)
    (htotal : (∑ j, y j) ≤ ∑ i, z i) (j : Fin n) :
    (∑ i, prefixTransport n z y i j) = y j := by
  have hj : j.val + 1 ≤ (n : ℕ) := by omega
  have htop : prefixMass n y (j.val + 1) ≤ ∑ i, z i := by
    have h := prefixMass_mono n y hy hj
    rw [prefixMass_total] at h
    exact h.trans htotal
  have hlo : prefixMass n y j ≤ ∑ i, z i :=
    (prefixMass_mono n y hy (Nat.le_succ j.val)).trans htop
  have h0 := prefixMass_nonneg n y hy j
  have h1 := prefixMass_nonneg n y hy (j.val + 1)
  have h := sum_prefixMass_diff n z (fun t => min t (prefixMass n y (j.val + 1)) -
    min t (prefixMass n y j))
  have heq : (∑ i, prefixTransport n z y i j) =
      ∑ i : Fin n, ((min (prefixMass n z (i.val + 1)) (prefixMass n y (j.val + 1)) -
        min (prefixMass n z (i.val + 1)) (prefixMass n y j)) -
        (min (prefixMass n z i) (prefixMass n y (j.val + 1)) -
          min (prefixMass n z i) (prefixMass n y j))) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold prefixTransport
    ring
  rw [heq, h, min_eq_right htop, min_eq_right hlo, min_eq_left h0, min_eq_left h1]
  simpa using prefixMass_step n y j

theorem prefixTransport_eq_zero_of_lt (n : ℕ+) (z y : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hy : y ∈ pitmanStanleyPolytope n z)
    (i j : Fin n) (hji : j < i) : prefixTransport n z y i j = 0 := by
  have hsource : prefixMass n y (j.val + 1) ≤ prefixMass n z (j.val + 1) := by
    simpa only [prefixMass_Iic] using hy.2 j
  have hbound : prefixMass n y (j.val + 1) ≤ prefixMass n z i :=
    hsource.trans (prefixMass_mono n z hz (by exact hji))
  have hbound' : prefixMass n y (j.val + 1) ≤ prefixMass n z (i.val + 1) :=
    hbound.trans (prefixMass_mono n z hz (Nat.le_succ i.val))
  have hlo := prefixMass_mono n y hy.1 (Nat.le_succ j.val)
  unfold prefixTransport
  rw [min_eq_right hbound', min_eq_right hbound, min_eq_right (hlo.trans hbound'),
    min_eq_right (hlo.trans hbound)]
  ring

/-- Reverse inclusion in PS02 Theorem 9 by an upper-triangular transportation matrix. -/
theorem pitmanStanleyPolytope_subset_minkowskiSum (n : ℕ+) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    pitmanStanleyPolytope n z ⊆ pitmanStanleyMinkowskiSum n z := by
  intro y hy
  have hnonneg := prefixTransport_nonneg n z y hz hy.1
  have hrow := sum_prefixTransport_row_le n z y hz
  have htotal : (∑ j, y j) ≤ ∑ i, z i := by
    have hn := n.pos
    let last : Fin n := ⟨(n : ℕ) - 1, by omega⟩
    have h := hy.2 last
    have hset : Finset.Iic last = Finset.univ := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      change j.val ≤ (n : ℕ) - 1
      have hj := j.isLt
      omega
    simpa only [hset] using h
  have hcol := sum_prefixTransport_col n z y hy.1 htotal
  have hzero : ∀ i, z i = 0 → ∀ j, prefixTransport n z y i j = 0 := by
    intro i hi j
    have hle := (Finset.single_le_sum (fun k _ => hnonneg i k) (Finset.mem_univ j)).trans (hrow i)
    rw [hi] at hle
    exact le_antisymm hle (hnonneg i j)
  let v : Fin n → Fin n → ℝ := fun i j => prefixTransport n z y i j / z i
  have hv : ∀ i, v i ∈ pitmanStanleySimplex n i := by
    intro i
    refine ⟨fun j => div_nonneg (hnonneg i j) (hz i), ?_, ?_⟩
    · intro j hji
      dsimp [v]
      rw [prefixTransport_eq_zero_of_lt n z y hz hy i j hji, zero_div]
    · dsimp [v]
      rw [← Finset.sum_div]
      by_cases hi : z i = 0
      · simp [hi]
      · exact (div_le_one (lt_of_le_of_ne (hz i) (Ne.symm hi))).mpr (hrow i)
  have hscale : ∀ i j, (z i • v i) j = prefixTransport n z y i j := by
    intro i j
    change z i * (prefixTransport n z y i j / z i) = _
    by_cases hi : z i = 0
    · rw [hi, hzero i hi j]
      simp
    · field_simp
  apply (Set.mem_fintype_sum _ _).mpr
  refine ⟨fun i => z i • v i, fun i => ⟨v i, hv i, rfl⟩, ?_⟩
  funext j
  simp only [Finset.sum_apply, hscale]
  exact hcol j

/-- PS02 Theorem 9 for the exact suffix simplices of the manuscript's remark. -/
theorem pitmanStanleyPolytope_eq_minkowskiSum (n : ℕ+) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    pitmanStanleyPolytope n z = pitmanStanleyMinkowskiSum n z :=
  Set.Subset.antisymm (pitmanStanleyPolytope_subset_minkowskiSum n z hz)
    (pitmanStanleyMinkowskiSum_subset n z hz)

end Parking

end
