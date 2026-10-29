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
public import Parking.Exchangeable

/-!
# The law of a uniform parking function as a word

The law of `π_n` viewed in `[n]^n`, its exchangeability (`lem:marginal`), and the expression of `P_{n,k}` and `μ_n` as coordinate laws of
this exchangeable law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Parking

/-- The law of the word `(π_n(1), …, π_n(n)) ∈ [n]^n`. -/
noncomputable def parkingWordLaw (n : ℕ+) : Measure (Fin n → Fin n) :=
  (uniformParking n : Measure (ParkingFunction n)).map fun a => a.1

/-- Permuting the coordinates of a parking function gives a parking function. -/
def permCoords (n : ℕ+) (σ : Equiv.Perm (Fin n)) : ParkingFunction n ≃ ParkingFunction n where
  toFun a := ⟨a.1 ∘ σ, (isParkingFunction_comp_perm_iff a.1 σ).2 a.2⟩
  invFun a := ⟨a.1 ∘ σ.symm, (isParkingFunction_comp_perm_iff a.1 σ.symm).2 a.2⟩
  left_inv a := Subtype.ext (by funext i; simp)
  right_inv a := Subtype.ext (by funext i; simp)

/-- The uniform law on a finite type is invariant under every bijection. -/
theorem uniformOn_univ_map_equiv {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (e : α ≃ α) :
    (uniformOn (Set.univ : Set α)).map e = uniformOn Set.univ := by
  refine Measure.ext_iff_singleton.2 fun y => ?_
  rw [Measure.map_apply (measurable_of_finite e) (measurableSet_singleton y)]
  have h : (e : α → α) ⁻¹' {y} = {e.symm y} := by
    ext x; simp [Equiv.eq_symm_apply]
  rw [h, uniformOn_univ, uniformOn_univ, Measure.count_singleton, Measure.count_singleton]

/-- The uniform parking function is exchangeable (`lem:marginal`). -/
theorem isExchangeableLaw_parkingWordLaw (n : ℕ+) : IsExchangeableLaw (parkingWordLaw n) := by
  intro σ
  have hcomp : (fun x : Fin n → Fin n => fun i => x (σ i)) ∘ (fun a : ParkingFunction n => a.1)
      = (fun a : ParkingFunction n => a.1) ∘ permCoords n σ := rfl
  unfold parkingWordLaw
  calc ((uniformParking n : Measure (ParkingFunction n)).map fun a => a.1).map
        (fun x : Fin n → Fin n => fun i => x (σ i))
      = (uniformParking n : Measure (ParkingFunction n)).map
          ((fun x : Fin n → Fin n => fun i => x (σ i)) ∘ fun a : ParkingFunction n => a.1) :=
        Measure.map_map (measurable_of_finite _) (measurable_of_finite _)
    _ = (uniformParking n : Measure (ParkingFunction n)).map
          ((fun a : ParkingFunction n => a.1) ∘ permCoords n σ) := by rw [hcomp]
    _ = ((uniformParking n : Measure (ParkingFunction n)).map (permCoords n σ)).map
          fun a => a.1 :=
        (Measure.map_map (measurable_of_finite _) (measurable_of_finite _)).symm
    _ = (uniformParking n : Measure (ParkingFunction n)).map fun a => a.1 := by
        rw [show (uniformParking n : Measure (ParkingFunction n)) = uniformOn Set.univ from rfl,
          uniformOn_univ_map_equiv]

/-- `P_{n,k}` is the law of the first `k` coordinates of the word `π_n`. -/
theorem firstCoordsLaw_eq_coordLaw (n : ℕ+) (k : ℕ) (hk : k ≤ n) :
    (firstCoordsLaw n k hk : Measure (Fin k → Fin n)) = coordLaw (parkingWordLaw n) hk := by
  rw [firstCoordsLaw, ProbabilityMeasure.toMeasure_map, coordLaw, parkingWordLaw,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

/-- `μ_n` is the law of any coordinate of `π_n`, by exchangeability. -/
theorem marginal_eq_coordMarginalLaw (n : ℕ+) (j : Fin n) :
    (marginal n : Measure (Fin n)) = coordMarginalLaw (parkingWordLaw n) j := by
  rw [(isExchangeableLaw_parkingWordLaw n).coordMarginalLaw_eq j ⟨0, n.pos⟩, marginal,
    ProbabilityMeasure.toMeasure_map, coordMarginalLaw, parkingWordLaw,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

end Parking

end
