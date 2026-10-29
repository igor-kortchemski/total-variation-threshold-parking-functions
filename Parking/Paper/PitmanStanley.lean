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

public import Mathlib.Data.PNat.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# The geometric objects in the Pitman–Stanley remark

The polytope is defined by its actual prefix inequalities, not by a generating
polynomial. These elementary geometric lemmas support the volume formula
and Lorentzian consequence proved in `Parking.Paper.PitmanStanleyFormula`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators Pointwise

namespace Parking

/-- The Pitman–Stanley polytope, with zero-based indices. -/
def pitmanStanleyPolytope (n : ℕ+) (z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∀ i, ∑ j ∈ Finset.Iic i, y j ≤ ∑ j ∈ Finset.Iic i, z j}

/-- The simplex spanned by zero and the coordinate vectors with index at least `i`. -/
def pitmanStanleySimplex (n : ℕ+) (i : Fin n) : Set (Fin n → ℝ) :=
  {y | (∀ j, 0 ≤ y j) ∧ (∀ j, j < i → y j = 0) ∧ ∑ j, y j ≤ 1}

/-- The genuine Minkowski sum of the scaled suffix simplices. -/
def pitmanStanleyMinkowskiSum (n : ℕ+) (z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  ∑ i, z i • pitmanStanleySimplex n i

/-- Closedness of the polytope follows from its finitely many linear inequalities. -/
theorem isClosed_pitmanStanleyPolytope (n : ℕ+) (z : Fin n → ℝ) :
    IsClosed (pitmanStanleyPolytope n z) := by
  change IsClosed ({y : Fin n → ℝ | ∀ i, 0 ≤ y i} ∩
    {y : Fin n → ℝ | ∀ i, ∑ j ∈ Finset.Iic i, y j ≤ ∑ j ∈ Finset.Iic i, z j})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

/-- The polytope contains zero for all nonnegative parameters, including boundary cases. -/
theorem zero_mem_pitmanStanleyPolytope (n : ℕ+) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ∈ pitmanStanleyPolytope n z := by
  constructor
  · simp
  · intro i
    simpa using Finset.sum_nonneg (fun j (_ : j ∈ Finset.Iic i) => hz j)

/-- Every coordinate in the polytope is at most the total parameter mass. -/
theorem pitmanStanleyPolytope_subset_box (n : ℕ+) (z : Fin n → ℝ) :
    pitmanStanleyPolytope n z ⊆ Set.Icc 0 (fun _ => ∑ i, z i) := by
  have hn := n.pos
  intro y hy
  refine ⟨hy.1, fun i => ?_⟩
  have hlast : (Finset.Iic (⟨(n : ℕ) - 1, by omega⟩ : Fin n)) = Finset.univ := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    change (j : ℕ) ≤ (n : ℕ) - 1
    have hj := j.isLt
    omega
  have htotal := hy.2 (⟨(n : ℕ) - 1, by omega⟩ : Fin n)
  rw [hlast] at htotal
  exact (Finset.single_le_sum (fun j _ => hy.1 j) (Finset.mem_univ i)).trans htotal

/-- In particular, the geometric volume is finite. -/
theorem isCompact_pitmanStanleyPolytope (n : ℕ+) (z : Fin n → ℝ) :
    IsCompact (pitmanStanleyPolytope n z) :=
  isCompact_Icc.of_isClosed_subset (isClosed_pitmanStanleyPolytope n z)
    (pitmanStanleyPolytope_subset_box n z)

/-- The actual Lebesgue volume of the prefix-inequality polytope is finite. -/
theorem volume_pitmanStanleyPolytope_ne_top (n : ℕ+) (z : Fin n → ℝ) :
    volume (pitmanStanleyPolytope n z) ≠ ⊤ :=
  (isCompact_pitmanStanleyPolytope n z).measure_ne_top

/-- The easy inclusion in PS02 Theorem 9, using actual Minkowski addition. -/
theorem pitmanStanleyMinkowskiSum_subset (n : ℕ+) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    pitmanStanleyMinkowskiSum n z ⊆ pitmanStanleyPolytope n z := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := (Set.mem_fintype_sum _ _).mp hy
  have hunonneg : ∀ i j, 0 ≤ u i j := by
    intro i j
    obtain ⟨v, hv, he⟩ := (hu i)
    rw [← he]
    exact mul_nonneg (hz i) (hv.1 j)
  refine ⟨fun j => ?_, fun j => ?_⟩
  · simp only [Finset.sum_apply]
    exact Finset.sum_nonneg fun i _ => hunonneg i j
  · simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    calc
      ∑ i, ∑ k ∈ Finset.Iic j, u i k ≤ ∑ i, if i ≤ j then z i else 0 := by
        apply Finset.sum_le_sum
        intro i _
        obtain ⟨v, hv, he⟩ := hu i
        rw [← he]
        simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        by_cases hij : i ≤ j
        · simp only [hij, ite_true]
          have hs : ∑ k ∈ Finset.Iic j, v k ≤ 1 :=
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun k _ _ => hv.1 k)).trans hv.2.2
          nlinarith [hz i]
        · simp only [hij, ite_false]
          have hs : ∑ k ∈ Finset.Iic j, v k = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            exact hv.2.1 k ((Finset.mem_Iic.mp hk).trans_lt (lt_of_not_ge hij))
          rw [hs, mul_zero]
      _ = ∑ i ∈ Finset.Iic j, z i := by
        simp only [← Finset.sum_filter]
        congr 1
        ext i
        simp

end Parking

end
