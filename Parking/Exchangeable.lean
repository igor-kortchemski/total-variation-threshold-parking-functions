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

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exchangeable laws on words

Laws on `[d]^N = Fin N → Fin d` that are invariant under permutations of the
coordinates, and the laws of their coordinate restrictions. The paper uses
exchangeability of the uniform parking function (`lem:marginal`) and of its initial segments (`lem:occupation_logconcavity`).

Adapted from §4 of the OpenMathModelFiles parallel formalization, including
`IsExchangeableLaw.coordLaw`, contributed there by an independent auditor. Changes
are limited to the namespace, module header and documentation. Source provenance
is recorded in `docs/PROVENANCE.md`.
-/

@[expose] public section

open MeasureTheory

namespace Parking

/-- A law on `[d]^N` invariant under permutations of coordinates. -/
def IsExchangeableLaw {N d : ℕ} (L : Measure (Fin N → Fin d)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), L.map (fun x => fun i => x (σ i)) = L

/-- The law of the first `k` coordinates under `L`. -/
noncomputable def coordLaw {N d : ℕ} (L : Measure (Fin N → Fin d)) {k : ℕ}
    (hk : k ≤ N) : Measure (Fin k → Fin d) :=
  L.map fun x => fun i => x (Fin.castLE hk i)

/-- The law of coordinate `j` under `L`. -/
noncomputable def coordMarginalLaw {N d : ℕ} (L : Measure (Fin N → Fin d))
    (j : Fin N) : Measure (Fin d) :=
  L.map fun x => x j

/-- The law of the coordinates in `S ⊆ [N]` under `L`. -/
noncomputable def restrictCoordLaw {N d : ℕ} (L : Measure (Fin N → Fin d))
    (S : Finset (Fin N)) : Measure (S → Fin d) :=
  L.map fun x => fun i => x i.1

/-- Permutation of `Fin N` acting by `σ` on the first `k` coordinates
and fixing the rest; auxiliary for `IsExchangeableLaw.coordLaw`. -/
noncomputable def tauEquiv {N : ℕ} {k : ℕ} (hk : k ≤ N) (σ : Equiv.Perm (Fin k)) :
    Fin N ≃ Fin N where
  toFun i := if h : i.val < k then Fin.castLE hk (σ ⟨i.val, h⟩) else i
  invFun j := if h : j.val < k then Fin.castLE hk (σ.symm ⟨j.val, h⟩) else j
  left_inv i := by
    by_cases hi : i.val < k
    · show (if h : (if h : i.val < k then Fin.castLE hk (σ ⟨i.val, h⟩) else i).val < k
        then Fin.castLE hk (σ.symm ⟨(if h : i.val < k then Fin.castLE hk (σ ⟨i.val, h⟩)
          else i).val, h⟩)
        else (if h : i.val < k then Fin.castLE hk (σ ⟨i.val, h⟩) else i)) = i
      rw [dite_eq_left hi, dite_eq_left (show ↑(Fin.castLE hk (σ ⟨i.val, hi⟩)) < k from
        (σ ⟨i.val, hi⟩).isLt)]
      rw [show (⟨↑(Fin.castLE hk (σ ⟨i.val, hi⟩)), _⟩ : Fin k) = σ ⟨i.val, hi⟩ from
        Fin.ext rfl]
      rw [Equiv.symm_apply_apply]
      exact Fin.ext rfl
    · show (if h : (if h : i.val < k then Fin.castLE hk (σ ⟨i.val, h⟩) else i).val < k
        then Fin.castLE hk (σ.symm ⟨(if h : i.val < k then Fin.castLE hk (σ ⟨i.val, h⟩)
          else i).val, h⟩)
        else (if h : i.val < k then Fin.castLE hk (σ ⟨i.val, h⟩) else i)) = i
      rw [dite_eq_right hi, dite_eq_right hi]
  right_inv j := by
    by_cases hj : j.val < k
    · show (if h : (if h : j.val < k then Fin.castLE hk (σ.symm ⟨j.val, h⟩) else j).val < k
        then Fin.castLE hk (σ ⟨(if h : j.val < k then Fin.castLE hk (σ.symm ⟨j.val, h⟩)
          else j).val, h⟩)
        else (if h : j.val < k then Fin.castLE hk (σ.symm ⟨j.val, h⟩) else j)) = j
      rw [dite_eq_left hj, dite_eq_left (show ↑(Fin.castLE hk (σ.symm ⟨j.val, hj⟩)) < k from
        (σ.symm ⟨j.val, hj⟩).isLt)]
      rw [show (⟨↑(Fin.castLE hk (σ.symm ⟨j.val, hj⟩)), _⟩ : Fin k) =
          σ.symm ⟨j.val, hj⟩ from Fin.ext rfl]
      rw [Equiv.apply_symm_apply]
      exact Fin.ext rfl
    · show (if h : (if h : j.val < k then Fin.castLE hk (σ.symm ⟨j.val, h⟩) else j).val < k
        then Fin.castLE hk (σ ⟨(if h : j.val < k then Fin.castLE hk (σ.symm ⟨j.val, h⟩)
          else j).val, h⟩)
        else (if h : j.val < k then Fin.castLE hk (σ.symm ⟨j.val, h⟩) else j)) = j
      rw [dite_eq_right hj, dite_eq_right hj]

lemma tauEquiv_castLE {N k : ℕ} (hk : k ≤ N) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    tauEquiv hk σ (Fin.castLE hk i) = Fin.castLE hk (σ i) := by
  show (if h : (Fin.castLE hk i).val < k
      then Fin.castLE hk (σ ⟨(Fin.castLE hk i).val, h⟩) else Fin.castLE hk i)
      = Fin.castLE hk (σ i)
  rw [dite_eq_left (show (Fin.castLE hk i).val < k from i.isLt)]
  exact congrArg (Fin.castLE hk) (Fin.ext rfl)

/-- The first-`k` marginal law of an exchangeable law on `[d]^N` is exchangeable. -/
theorem IsExchangeableLaw.coordLaw {N d : ℕ} (L : Measure (Fin N → Fin d))
    (hexch : IsExchangeableLaw L) {k : ℕ} (hk : k ≤ N) :
    IsExchangeableLaw (coordLaw L hk) := by
  intro σ
  have hex := hexch (tauEquiv hk σ)
  have h1 : (fun y : Fin k → Fin d => fun i => y (σ i)) ∘
        (fun x : Fin N → Fin d => fun i => x (Fin.castLE hk i))
      = (fun x : Fin N → Fin d => fun i => x (tauEquiv hk σ (Fin.castLE hk i))) := by
    funext x i; simp only [Function.comp_apply, tauEquiv_castLE]
  have h2 : (fun x : Fin N → Fin d => fun i => x (tauEquiv hk σ (Fin.castLE hk i)))
      = (fun x : Fin N → Fin d => fun i => x (Fin.castLE hk i)) ∘
        (fun x : Fin N → Fin d => fun j => x (tauEquiv hk σ j)) := rfl
  calc
    (L.map (fun x : Fin N → Fin d => fun i => x (Fin.castLE hk i))).map
        (fun y : Fin k → Fin d => fun i => y (σ i))
        = L.map ((fun y : Fin k → Fin d => fun i => y (σ i)) ∘
            (fun x : Fin N → Fin d => fun i => x (Fin.castLE hk i))) :=
          Measure.map_map (measurable_of_finite _) (measurable_of_finite _)
    _ = L.map (fun x : Fin N → Fin d =>
          fun i => x (tauEquiv hk σ (Fin.castLE hk i))) := by rw [h1]
    _ = L.map ((fun x : Fin N → Fin d => fun i => x (Fin.castLE hk i)) ∘
          (fun x : Fin N → Fin d => fun j => x (tauEquiv hk σ j))) := by rw [h2]
    _ = (L.map (fun x : Fin N → Fin d => fun j => x (tauEquiv hk σ j))).map
          (fun x : Fin N → Fin d => fun i => x (Fin.castLE hk i)) :=
          (Measure.map_map (measurable_of_finite _) (measurable_of_finite _)).symm
    _ = L.map (fun x : Fin N → Fin d => fun i => x (Fin.castLE hk i)) := by rw [hex]

/-- The one-coordinate marginals of an exchangeable law coincide. -/
theorem IsExchangeableLaw.coordMarginalLaw_eq {N d : ℕ} {L : Measure (Fin N → Fin d)}
    (hexch : IsExchangeableLaw L) (i j : Fin N) :
    coordMarginalLaw L i = coordMarginalLaw L j := by
  have h := hexch (Equiv.swap i j)
  calc coordMarginalLaw L i
      = (L.map fun x => fun l => x (Equiv.swap i j l)).map (fun x => x j) := by
        rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
        unfold coordMarginalLaw
        congr 1
        funext x
        simp
    _ = coordMarginalLaw L j := by rw [h]; rfl

end Parking

end
