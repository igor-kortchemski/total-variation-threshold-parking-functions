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

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The reverse Cauchy–Schwarz inequality for bilinear forms

A real form
`B : (Fin d → ℝ) → (Fin d → ℝ) → ℝ` satisfies `RevCS B` when
`B x x * B y y ≤ B x y ^ 2` whenever `0 < B x x`. For a symmetric bilinear form this is
equivalent to having at most one positive eigenvalue; no eigenvalue is needed to state it.

Main results:

- `revCS_of_at`: the transfer lemma. For a symmetric bilinear form, the inequality at one
  point `w` with `0 < B w w` gives `RevCS B`. The proof uses the identity
  `B x x * B z z = (a * B x x - b * B x y) ^ 2 + b ^ 2 * Δ` for `z = a • x - b • y`,
  `a = B w y`, `b = B w x`, `Δ = B x x * B y y - B x y ^ 2`, which also covers `z = 0`.
- `revCS_rankOne_sub`: Aczél's inequality, "rank one minus positive semidefinite is
  RevCS". This is the step concluding the proof of [BH20, Lemma 3.11] (Brändén–Huh,
  *Lorentzian polynomials*, arXiv:1902.03719).
- `RevCS.of_tendsto`: `RevCS` passes to pointwise limits along any nontrivial filter.
- `revCS_zero`: the zero form is RevCS.
-/

public section

open Filter Topology

namespace Parking

/-- The reverse Cauchy–Schwarz property of a real form `B` on `ℝ^d`: for all `x, y`, if
`0 < B x x` then `B x x * B y y ≤ B x y ^ 2`. For a symmetric bilinear form this means
"at most one positive eigenvalue". -/
@[expose] def RevCS {d : ℕ} (B : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) : Prop :=
  ∀ x y, 0 < B x x → B x x * B y y ≤ B x y ^ 2

/-- The zero form satisfies `RevCS` (vacuously). -/
theorem revCS_zero {d : ℕ} : RevCS fun _ _ : Fin d → ℝ => (0 : ℝ) :=
  fun _ _ h => absurd h (lt_irrefl 0)

/-- **Transfer lemma.** Let `B` be a symmetric bilinear form and `w` a point with
`0 < B w w`. If the reverse Cauchy–Schwarz inequality `B z z * B w w ≤ B w z ^ 2` holds at
`w` for every `z`, then it holds everywhere: `RevCS B`. -/
theorem revCS_of_at {d : ℕ} (B : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (w : Fin d → ℝ)
    (hsymm : ∀ x y, B x y = B y x) (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul : ∀ (c : ℝ) x y, B (c • x) y = c * B x y) (hw : 0 < B w w)
    (h : ∀ z, B z z * B w w ≤ B w z ^ 2) : RevCS B := by
  have hlin : ∀ (a b : ℝ) (u v t : Fin d → ℝ), B (a • u + b • v) t = a * B u t + b * B v t :=
    fun a b u v t => by rw [hadd, hsmul, hsmul]
  intro x y hx
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz⟩ : ∃ z, z = B w y • x + (-B w x) • y := ⟨_, rfl⟩
  -- `B w z = 0`
  have hwz : B w z = 0 := by
    rw [hsymm, hz, hlin, hsymm x w, hsymm y w]
    ring
  -- expansion of `B z z`
  have hzx : B x z = B w y * B x x + -B w x * B y x := by rw [hsymm, hz, hlin]
  have hzy : B y z = B w y * B x y + -B w x * B y y := by rw [hsymm, hz, hlin]
  have hzz : B z z = B w y * B x z + -B w x * B y z := by
    nth_rw 1 [hz]
    rw [hlin]
  have hzz' : B z z = B w y ^ 2 * B x x - 2 * B w y * B w x * B x y + B w x ^ 2 * B y y := by
    rw [hzz, hzx, hzy, hsymm y x]
    ring
  have hzw := h z
  rw [hwz] at hzw
  -- `B z z ≤ 0`
  have hzz0 : B z z ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := mul_pos hpos hw
    linarith
  have key : B x x * B z z =
      (B w y * B x x - B w x * B x y) ^ 2 + B w x ^ 2 * (B x x * B y y - B x y ^ 2) := by
    rw [hzz']
    ring
  have hb : B w x ^ 2 * (B x x * B y y - B x y ^ 2) ≤ 0 := by
    have h1 := mul_nonpos_of_nonneg_of_nonpos hx.le hzz0
    linarith [sq_nonneg (B w y * B x x - B w x * B x y)]
  have hb0 : B w x ^ 2 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := mul_pos hpos (sub_pos.2 hcon)
    linarith
  have hxw := h x
  have := mul_pos hx hw
  linarith

/-- **Aczél's inequality.** A rank-one form minus a positive semidefinite symmetric
bilinear form satisfies `RevCS`. This is the final step of the proof of [BH20, Lemma 3.11]:
project `y` on the kernel of `ℓ` along `x`, and use the nonnegativity of `S`. -/
theorem revCS_rankOne_sub {d : ℕ} (ℓ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (S : LinearMap.BilinForm ℝ (Fin d → ℝ)) (hS : S.IsSymm) (hpos : ∀ x, 0 ≤ S x x) :
    RevCS fun x y => ℓ x * ℓ y - S x y := by
  intro x y hx
  simp only at hx ⊢
  have hu := hpos (ℓ x • y - ℓ y • x)
  have hexp : S (ℓ x • y - ℓ y • x) (ℓ x • y - ℓ y • x) =
      ℓ x ^ 2 * S y y - 2 * ℓ x * ℓ y * S x y + ℓ y ^ 2 * S x x := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hS.eq y x]
    ring
  rw [hexp] at hu
  have hSx := hpos x
  have hp : ℓ x ≠ 0 := by
    rintro hp
    rw [hp] at hx
    linarith
  have hp2 : 0 < ℓ x ^ 2 := by positivity
  have key : ℓ x ^ 2 * ((ℓ x * ℓ y - S x y) ^ 2 - (ℓ x * ℓ x - S x x) * (ℓ y * ℓ y - S y y)) =
      (ℓ x * S x y - ℓ y * S x x) ^ 2 + (ℓ x * ℓ x - S x x) *
        (ℓ x ^ 2 * S y y - 2 * ℓ x * ℓ y * S x y + ℓ y ^ 2 * S x x) := by
    ring
  have hnn : 0 ≤ ℓ x ^ 2 *
      ((ℓ x * ℓ y - S x y) ^ 2 - (ℓ x * ℓ x - S x x) * (ℓ y * ℓ y - S y y)) := by
    rw [key]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hx.le hu)
  have := nonneg_of_mul_nonneg_right hnn hp2
  linarith

/-- **Closedness.** `RevCS` passes to pointwise limits: if `B i x y → B₀ x y` along a
nontrivial filter for all `x, y`, and `RevCS (B i)` holds eventually, then `RevCS B₀`. -/
theorem RevCS.of_tendsto {d : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    {B : ι → (Fin d → ℝ) → (Fin d → ℝ) → ℝ} {B₀ : (Fin d → ℝ) → (Fin d → ℝ) → ℝ}
    (hB : ∀ x y, Tendsto (fun i => B i x y) l (𝓝 (B₀ x y)))
    (h : ∀ᶠ i in l, RevCS (B i)) : RevCS B₀ := by
  intro x y hx
  have hev : ∀ᶠ i in l, B i x x * B i y y ≤ B i x y ^ 2 := by
    filter_upwards [h, (hB x x).eventually_const_lt hx] with i hi hpos
    exact hi x y hpos
  exact le_of_tendsto_of_tendsto (((hB x x).mul (hB y y))) ((hB x y).pow 2) hev

end Parking
