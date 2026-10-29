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

public import Parking.Paper.StrongLogConcavity
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Positive index and reverse Cauchy–Schwarz

The positive index is the maximal dimension of a subspace on which a quadratic
form is positive definite. This supplies an independent algebraic formulation of
“at most one positive eigenvalue”, without defining a signature condition through
log-concavity or through the reverse Cauchy–Schwarz inequality.
-/

public section

namespace Parking

open LinearMap.BilinForm

/-- Reverse Cauchy–Schwarz forces every positive-definite subspace to have
dimension at most one. -/
theorem sigPos_le_one_of_revCS {d : ℕ} (B : LinearMap.BilinForm ℝ (Fin d → ℝ))
    (hB : RevCS fun u v => B u v) : sigPos B.toQuadraticMap ≤ 1 := by
  obtain ⟨V, hdim, hV⟩ := exists_finrank_eq_sigPos_and_posDef B.toQuadraticMap
  rw [← hdim]
  by_cases hzero : ∀ u : V, u = 0
  · have : Subsingleton V := ⟨fun u v => (hzero u).trans (hzero v).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    omega
  push Not at hzero
  obtain ⟨u, hu⟩ := hzero
  let ℓ : V →ₗ[ℝ] ℝ := (B u).comp V.subtype
  have hinj : Function.Injective ℓ := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    have hposu : 0 < B u u := hV u hu
    have hposv : 0 < B v v := hV v hv0
    have h := hB u v hposu
    dsimp only at h
    change B u v = 0 at hv
    rw [hv] at h
    have := mul_pos hposu hposv
    nlinarith
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/-- A positive-index bound rules out two orthogonal vectors with positive
squares: their span would be a two-dimensional positive-definite subspace. -/
theorem bilin_nonpos_of_sigPos_le_one {d : ℕ}
    (B : LinearMap.BilinForm ℝ (Fin d → ℝ)) (hB : ∀ u v, B u v = B v u)
    (hsig : sigPos B.toQuadraticMap ≤ 1) {u v : Fin d → ℝ}
    (hu : 0 < B u u) (huv : B u v = 0) : B v v ≤ 0 := by
  by_contra hv
  push Not at hv
  have hune : u ≠ 0 := by rintro rfl; simp at hu
  have hlin : LinearIndependent ℝ ![u, v] := by
    rw [LinearIndependent.pair_iff' hune]
    intro a ha
    have : a * B u u = 0 := by
      rw [← huv, ← ha, smul_right]
    have ha0 : a = 0 := (mul_eq_zero.mp this).resolve_right hu.ne'
    rw [ha0, zero_smul] at ha
    rw [← ha] at hv
    simp at hv
  let V := Submodule.span ℝ ({u, v} : Set (Fin d → ℝ))
  have hdim : Module.finrank ℝ V = 2 := by
    have hrange : Set.range ![u, v] = ({u, v} : Set (Fin d → ℝ)) := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      aesop
    have hdim' := finrank_span_eq_card hlin
    change Module.finrank ℝ (Submodule.span ℝ (Set.range ![u, v])) = 2 at hdim'
    rw [hrange] at hdim'
    exact hdim'
  have hpos : (B.toQuadraticMap.restrict V).PosDef := by
    intro z hz
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp z.property
    have hab0 : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      apply Subtype.ext
      simpa [h.1, h.2] using hab.symm
    change 0 < B z z
    rw [← hab]
    simp only [add_left, add_right, smul_left, smul_right, huv, hB v u,
      mul_zero, add_zero, zero_add]
    rcases hab0 with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
  have := le_sigPos_of_posDef B.toQuadraticMap hpos
  omega

/-- The independent positive-index condition is equivalent to reverse
Cauchy–Schwarz for a real symmetric bilinear form. -/
theorem sigPos_le_one_iff_revCS {d : ℕ}
    (B : LinearMap.BilinForm ℝ (Fin d → ℝ)) (hB : ∀ u v, B u v = B v u) :
    sigPos B.toQuadraticMap ≤ 1 ↔ RevCS (fun u v => B u v) := by
  constructor
  · intro h u v hu
    exact bilin_reverse_cauchySchwarz B hB (B u)
      (fun w hw => bilin_nonpos_of_sigPos_le_one B hB h hu hw) hu v
  · exact sigPos_le_one_of_revCS B

end Parking

end
