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

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Borel weights

The Borel probabilities `q_i = e^{-i} i^{i-1} / i!`, `i ≥ 1`, which enter the marginal
formula of Diaconis and Hicks in the proof of `lem:marginal`
(`lem:marginal`), and the identity
`q_1 q_n / q_{n+1} = (n / (n+1))^{n-1}` behind the endpoint relation
`1 + g_n(n) = δ_n(1)` (`lem:marginal`).

Adapted from the OpenMathModelFiles parallel formalization: `borelW` and
`borelW_one_mul_borelW_div_succ` (the latter contributed by an independent auditor),
renamed `borelWeight` and `borelWeight_one_mul_div_succ`. Source provenance is
recorded in `docs/PROVENANCE.md`.
-/

@[expose] public section

namespace Parking

/-- The Borel weight `q_i = e^{-i} i^{i-1} / i!` (`lem:marginal`). The source uses it
for `i ≥ 1` only; at `i = 0` the formula evaluates to `1`, a value never used. -/
noncomputable def borelWeight (i : ℕ) : ℝ :=
  Real.exp (-(i : ℝ)) * (i : ℝ) ^ (i - 1) / (Nat.factorial i : ℝ)

/-- `q_1 q_n / q_{n+1} = (n / (n+1))^{n-1}`. -/
theorem borelWeight_one_mul_div_succ (n : ℕ) (hn : 2 ≤ n) :
    borelWeight 1 * borelWeight n / borelWeight (n + 1) = ((n : ℝ) / (n + 1)) ^ (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  have hns : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  have h1 : borelWeight 1 = Real.exp (-1) := by simp [borelWeight]
  have h2 : borelWeight n = Real.exp (-(n : ℝ)) * (n : ℝ) ^ (n - 1) / (Nat.factorial n : ℝ) := by
    simp [borelWeight]
  have h3 : borelWeight (n + 1) =
      Real.exp (-((n : ℝ) + 1)) * ((n : ℝ) + 1) ^ n / (Nat.factorial (n + 1) : ℝ) := by
    simp only [borelWeight]
    push_cast
    simp
  have hfac : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hexp : Real.exp (-1) * Real.exp (-(n : ℝ)) / Real.exp (-((n : ℝ) + 1)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_sub]
    have : -(1 : ℝ) + -(n : ℝ) - -((n : ℝ) + 1) = 0 := by ring
    rw [this, Real.exp_zero]
  have key : borelWeight 1 * borelWeight n / borelWeight (n + 1)
      = (Real.exp (-1) * Real.exp (-(n : ℝ)) / Real.exp (-((n : ℝ) + 1))) *
        (((n : ℝ) ^ (n - 1) / (Nat.factorial n : ℝ)) /
          (((n : ℝ) + 1) ^ n / (Nat.factorial (n + 1) : ℝ))) := by
    rw [h1, h2, h3]; ring
  rw [key, hexp, one_mul, hfac, div_pow]
  have hpow : ((n : ℝ) + 1) ^ n = ((n : ℝ) + 1) ^ (n - 1) * ((n : ℝ) + 1) := by
    conv_lhs => rw [← hns]
    rw [pow_succ]
    simp [hns]
  rw [hpow]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnp1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hnfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp

end Parking

end
