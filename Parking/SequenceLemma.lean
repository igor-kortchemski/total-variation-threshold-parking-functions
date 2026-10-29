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

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The quadratic contraction of a sequence

The elementary step of the proof of `lem:sample_entropy`: if `D 1 = 0` and `m D(m-1) ≤ (m-2) D(m)` for `2 ≤ m ≤ N`, then
`D(m) / (m(m-1))` is nondecreasing, hence `D(k) ≤ k(k-1)/(N(N-1)) · D(N)`.

Adapted from `ParkingThreshold.sequence_lemma` in the OpenMathModelFiles parallel
formalization, with changes to the namespace, imports and documentation. Source
provenance is recorded in `docs/PROVENANCE.md`.
-/

public section

namespace Parking

/-- The elementary sequence lemma underlying the entropy contraction in the
proof of the paper's Lemma 4.1: if `D 1 = 0` and
`m·D(m-1) ≤ (m-2)·D m` for all `2 ≤ m ≤ N` (real arithmetic), then
`D(k) ≤ (k(k-1))/(N(N-1))·D(N)` for all `1 ≤ k ≤ N`. No sign hypotheses on
`D` are needed, and none occur. -/
theorem sequence_lemma {N : ℕ} (hN : 2 ≤ N) (D : ℕ → ℝ) (hD1 : D 1 = 0)
    (hrec : ∀ m : ℕ, 2 ≤ m → m ≤ N → (m : ℝ) * D (m - 1) ≤ ((m : ℝ) - 2) * D m)
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    D k ≤ ((k : ℝ) * ((k : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1)) * D N := by
  have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdenN : 0 < (N : ℝ) * ((N : ℝ) - 1) := by
    have h1 : (0 : ℝ) < (N : ℝ) := by positivity
    have h2 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    positivity
  -- One-step monotonicity of `D m / (m (m-1))` on `2 ≤ m`, `m + 1 ≤ N`.
  have hstep : ∀ m : ℕ, 2 ≤ m → m + 1 ≤ N →
      D m / ((m : ℝ) * ((m : ℝ) - 1)) ≤
        D (m + 1) / (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1)) := by
    intro m hm2 hmN
    have h2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hm1 : (0 : ℝ) < (m : ℝ) := by linarith
    have hmm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    have hden1 : 0 < (m : ℝ) * ((m : ℝ) - 1) := by positivity
    have hden2 : 0 < ((m : ℝ) + 1) * m := by positivity
    have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
    have h := hrec (m + 1) (by omega) hmN
    rw [Nat.add_sub_cancel] at h
    push_cast at h
    -- `h : ((m:ℝ) + 1) * D m ≤ ((m:ℝ) + 1 - 2) * D (m + 1)`
    have h' : ((m : ℝ) + 1) * D m ≤ ((m : ℝ) - 1) * D (m + 1) := by linarith
    have h'' : (m : ℝ) * (((m : ℝ) + 1) * D m) ≤
        (m : ℝ) * (((m : ℝ) - 1) * D (m + 1)) :=
      mul_le_mul_of_nonneg_left h' hm1.le
    rw [div_le_div_iff₀ hden1]
    · rw [hcast, show ((m : ℝ) + 1) - 1 = (m : ℝ) from by ring]
      -- goal: `D m * ((m+1) * m) ≤ D (m+1) * (m * (m-1))`
      nlinarith [h'']
    · rw [hcast, show ((m : ℝ) + 1) - 1 = (m : ℝ) from by ring]
      exact hden2
  -- Chain monotonicity from `m` up to `N`.
  have chain : ∀ m : ℕ, 2 ≤ m → m ≤ N →
      D m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ D N / ((N : ℝ) * ((N : ℝ) - 1)) := by
    intro m hm2 hmN
    have key : ∀ t : ℕ, m + t ≤ N →
        D m / ((m : ℝ) * ((m : ℝ) - 1)) ≤
          D (m + t) / (((m + t : ℕ) : ℝ) * (((m + t : ℕ) : ℝ) - 1)) := fun t => by
      induction t with
      | zero => intro _; simp
      | succ s ih =>
          intro hle
          exact le_trans (ih (by omega)) (hstep (m + s) (by omega) hle)
    have := key (N - m) (by omega)
    rwa [Nat.add_sub_cancel' hmN] at this
  -- Assemble.
  rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
  · -- `k = 1`: both sides vanish.
    simp [hD1]
  · -- `2 ≤ k`: clear denominators.
    have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hden1 : 0 < (k : ℝ) * ((k : ℝ) - 1) := by positivity
    have hNk : D k / ((k : ℝ) * ((k : ℝ) - 1)) ≤ D N / ((N : ℝ) * ((N : ℝ) - 1)) :=
      chain k hk2 hkN
    calc
      D k = (D k / ((k : ℝ) * ((k : ℝ) - 1))) * ((k : ℝ) * ((k : ℝ) - 1)) := by
        field_simp
      _ ≤ (D N / ((N : ℝ) * ((N : ℝ) - 1))) * ((k : ℝ) * ((k : ℝ) - 1)) := by
        exact mul_le_mul_of_nonneg_right hNk hden1.le
      _ = ((k : ℝ) * ((k : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1)) * D N := by
        field_simp

end Parking

end
