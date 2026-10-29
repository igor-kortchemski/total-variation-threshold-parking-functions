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

public import Parking.Khintchine
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The Marcinkiewicz–Zygmund inequality with exponent one, by symmetrization

The only project import is `Parking.Khintchine`, which depends on Mathlib only.

Let `α` be a finite type, `M : α → ℝ` a probability weight and `u : α → ℝ` centred under `M`:
`M ≥ 0`, `∑ a, M a = 1` and `∑ a, M a * u a = 0`. For `x : Fin k → α` put
`W x = ∏ r, M (x r)`, the law of `k` independent coordinates of law `M`, and `U_r = u (x r)`.
The main result is the Marcinkiewicz–Zygmund inequality with exponent one
(`marcinkiewiczZygmund_one`):

$$
\frac1{2\sqrt3}\,\mathbb E\Bigl(\sum_rU_r^2\Bigr)^{1/2}\le\mathbb E\Bigl\lvert\sum_rU_r\Bigr\rvert
\le2\,\mathbb E\Bigl(\sum_rU_r^2\Bigr)^{1/2}.
$$

The proof uses symmetrization with an
independent copy `y : Fin k → α` of `x`:

* (J) *Jensen in the copy* (`abs_sum_mul_le_sum_prod_mul_abs`): for all coefficients `c`,
  `|∑ r, c_r U_r| ≤ 𝔼_y |∑ r, c_r (U_r - U'_r)|`. It uses only the centring of `u`
  (`sum_prod_mul_eq_zero`) and the triangle inequality.
* (W) *Swap* (`sum_sum_prod_mul_abs_sum_ite_neg`): for every sign pattern `ε`, exchanging
  `x r` and `y r` for the coordinates `r` with a negative sign is an involution of
  `(Fin k → α) × (Fin k → α)` that preserves the weight `W x W y`, so the signed differences
  `∑ r, ε_r (U_r - U'_r)` and the plain differences `∑ r, (U_r - U'_r)` have the same
  absolute first moment.
* Khintchine's inequality (`khintchine_one`) is applied pointwise, and the upper bound ends
  with the triangle inequality in `ℓ²` (`sqrt_sum_sub_sq_le`).
-/

public section

namespace Parking

open Finset

/-! ### Product weights -/

/-- The product weight of a probability weight has total mass one:
`∑ x : Fin k → α, ∏ r, M (x r) = 1` when `∑ a, M a = 1`. -/
theorem sum_prod_eq_one {α : Type*} [Fintype α] (M : α → ℝ) (hM1 : ∑ a, M a = 1) (k : ℕ) :
    ∑ x : Fin k → α, ∏ r, M (x r) = 1 := by
  have h := Fintype.prod_sum fun (_ : Fin k) (a : α) => M a
  rw [← h, hM1, Finset.prod_const_one]

/-- **Centring under the product weight**: if `∑ a, M a * u a = 0`, then for every coordinate
`r`, `∑ y : Fin k → α, (∏ r', M (y r')) * u (y r) = 0`. -/
theorem sum_prod_mul_eq_zero {α : Type*} [Fintype α] (M u : α → ℝ)
    (hu : ∑ a, M a * u a = 0) {k : ℕ} (r : Fin k) :
    ∑ y : Fin k → α, (∏ r', M (y r')) * u (y r) = 0 := by
  have key := Fintype.prod_sum fun (i : Fin k) (a : α) => M a * if i = r then u a else 1
  calc ∑ y : Fin k → α, (∏ r', M (y r')) * u (y r)
      = ∑ y : Fin k → α, ∏ i, (M (y i) * if i = r then u (y i) else 1) :=
        Finset.sum_congr rfl fun y _ => by
          rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ r]
          simp
    _ = ∏ i, ∑ a, (M a * if i = r then u a else 1) := key.symm
    _ = 0 := Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hu])

/-- The double expectation of `F x + F y` under two independent product weights is twice the
expectation of `F`. -/
theorem sum_sum_prod_mul_add {α : Type*} [Fintype α] (M : α → ℝ) (hM1 : ∑ a, M a = 1)
    {k : ℕ} (F : (Fin k → α) → ℝ) :
    ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) * (F x + F y) =
      2 * ∑ x : Fin k → α, (∏ r, M (x r)) * F x := by
  have h1 := sum_prod_eq_one M hM1 k
  calc ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) * (F x + F y)
      = ∑ x : Fin k → α, ∑ y : Fin k → α, ((∏ r, M (x r)) * F x) * (∏ r, M (y r)) +
          ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * ((∏ r, M (y r)) * F y) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
    _ = 2 * ∑ x : Fin k → α, (∏ r, M (x r)) * F x := by
        rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, h1]
        ring

/-! ### Jensen in the independent copy -/

/-- **Jensen in the independent copy** (lemma (J)). For a centred `u` and arbitrary
coefficients `c`, `|∑ r, c_r u (x r)| ≤ ∑ y, (∏ r, M (y r)) |∑ r, c_r (u (x r) - u (y r))|`.
Symmetry of `u` is not needed. -/
theorem abs_sum_mul_le_sum_prod_mul_abs {α : Type*} [Fintype α] (M u : α → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) {k : ℕ}
    (c : Fin k → ℝ) (x : Fin k → α) :
    |∑ r, c r * u (x r)| ≤
      ∑ y : Fin k → α, (∏ r, M (y r)) * |∑ r, c r * (u (x r) - u (y r))| := by
  have hW : ∀ y : Fin k → α, 0 ≤ ∏ r, M (y r) := fun y => Finset.prod_nonneg fun r _ => hM _
  have hmean : ∑ y : Fin k → α, (∏ r, M (y r)) * ∑ r, c r * (u (x r) - u (y r)) =
      ∑ r, c r * u (x r) := by
    calc ∑ y : Fin k → α, (∏ r, M (y r)) * ∑ r, c r * (u (x r) - u (y r))
        = ∑ y : Fin k → α, ((∏ r, M (y r)) * ∑ r, c r * u (x r) -
            ∑ r, c r * ((∏ r', M (y r')) * u (y r))) :=
          Finset.sum_congr rfl fun y _ => by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun r _ => by ring
      _ = (∑ y : Fin k → α, ∏ r, M (y r)) * ∑ r, c r * u (x r) -
            ∑ r, c r * ∑ y : Fin k → α, (∏ r', M (y r')) * u (y r) := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = ∑ r, c r * u (x r) := by
          simp only [sum_prod_eq_one M hM1, sum_prod_mul_eq_zero M u hu, mul_zero,
            Finset.sum_const_zero, one_mul, sub_zero]
  calc |∑ r, c r * u (x r)|
      = |∑ y : Fin k → α, (∏ r, M (y r)) * ∑ r, c r * (u (x r) - u (y r))| := by rw [hmean]
    _ ≤ ∑ y : Fin k → α, |(∏ r, M (y r)) * ∑ r, c r * (u (x r) - u (y r))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y : Fin k → α, (∏ r, M (y r)) * |∑ r, c r * (u (x r) - u (y r))| :=
        Finset.sum_congr rfl fun y _ => by rw [abs_mul, abs_of_nonneg (hW y)]

/-- Lemma (J) for a sign pattern `ε`:
`|∑ r, ε_r u (x r)| ≤ ∑ y, (∏ r, M (y r)) |∑ r, ε_r (u (x r) - u (y r))|`. -/
theorem abs_sum_ite_neg_le_sum_prod_mul_abs {α : Type*} [Fintype α] (M u : α → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) {k : ℕ}
    (ε : Fin k → Bool) (x : Fin k → α) :
    |∑ r, (if ε r then u (x r) else -u (x r))| ≤
      ∑ y : Fin k → α, (∏ r, M (y r)) *
        |∑ r, (if ε r then u (x r) - u (y r) else -(u (x r) - u (y r)))| := by
  have h := abs_sum_mul_le_sum_prod_mul_abs M u hM hM1 hu (fun r => if ε r then 1 else -1) x
  have e : ∀ (v : ℝ) (r : Fin k), (if ε r then (1 : ℝ) else -1) * v = if ε r then v else -v := by
    intro v r
    cases ε r <;> simp
  simpa only [e] using h

/-- Lemma (J) with all coefficients equal to one:
`|∑ r, u (x r)| ≤ ∑ y, (∏ r, M (y r)) |∑ r, (u (x r) - u (y r))|`. -/
theorem abs_sum_le_sum_prod_mul_abs {α : Type*} [Fintype α] (M u : α → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) {k : ℕ}
    (x : Fin k → α) :
    |∑ r, u (x r)| ≤ ∑ y : Fin k → α, (∏ r, M (y r)) * |∑ r, (u (x r) - u (y r))| := by
  simpa only [one_mul] using abs_sum_mul_le_sum_prod_mul_abs M u hM hM1 hu (fun _ => 1) x

/-! ### The swap involution -/

/-- **Swap lemma** (lemma (W)). For every sign pattern `ε`, the signed differences
`∑ r, ε_r (u (x r) - u (y r))` and the plain differences `∑ r, (u (x r) - u (y r))` have the
same absolute first moment under the weight `(∏ r, M (x r)) (∏ r, M (y r))`. The proof
exchanges `x r` and `y r` for the coordinates `r` with `ε r = false`; this involution
preserves the weight. No property of `M` or `u` is used. -/
theorem sum_sum_prod_mul_abs_sum_ite_neg {α : Type*} [Fintype α] (M u : α → ℝ) {k : ℕ}
    (ε : Fin k → Bool) :
    ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) *
        |∑ r, (if ε r then u (x r) - u (y r) else -(u (x r) - u (y r)))| =
      ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) *
        |∑ r, (u (x r) - u (y r))| := by
  let σ : (Fin k → α) × (Fin k → α) → (Fin k → α) × (Fin k → α) := fun p =>
    (fun r => if ε r then p.1 r else p.2 r, fun r => if ε r then p.2 r else p.1 r)
  have hσ : Function.Involutive σ := by
    rintro ⟨x, y⟩
    refine Prod.ext (funext fun r => ?_) (funext fun r => ?_) <;>
      · simp only [σ]
        cases ε r <;> rfl
  have h := Fintype.sum_equiv (hσ.toPerm σ)
    (fun p : (Fin k → α) × (Fin k → α) => (∏ r, M (p.1 r)) * (∏ r, M (p.2 r)) *
        |∑ r, (if ε r then u (p.1 r) - u (p.2 r) else -(u (p.1 r) - u (p.2 r)))|)
    (fun p => (∏ r, M (p.1 r)) * (∏ r, M (p.2 r)) * |∑ r, (u (p.1 r) - u (p.2 r))|)
    (by
      rintro ⟨x, y⟩
      simp only [Function.Involutive.coe_toPerm, σ]
      congr 1
      · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun r _ => ?_
        cases ε r
        · simp only [Bool.false_eq_true, ↓reduceIte, mul_comm]
        · simp only [↓reduceIte]
      · congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        cases ε r
        · simp only [Bool.false_eq_true, ↓reduceIte, neg_sub]
        · simp only [↓reduceIte])
  simpa only [Fintype.sum_prod_type] using h

/-! ### The triangle inequality in `ℓ²` -/

/-- **Triangle inequality in `ℓ²`** for finite sums:
`√(∑ (p - q)²) ≤ √(∑ p²) + √(∑ q²)`. -/
theorem sqrt_sum_sub_sq_le {ι : Type*} (s : Finset ι) (p q : ι → ℝ) :
    √(∑ i ∈ s, (p i - q i) ^ 2) ≤ √(∑ i ∈ s, p i ^ 2) + √(∑ i ∈ s, q i ^ 2) := by
  have hP : 0 ≤ ∑ i ∈ s, p i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hQ : 0 ≤ ∑ i ∈ s, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : |∑ i ∈ s, p i * q i| ≤ √(∑ i ∈ s, p i ^ 2) * √(∑ i ∈ s, q i ^ 2) := by
    rw [← Real.sqrt_mul hP]
    exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq s p q)
  have hexp : ∑ i ∈ s, (p i - q i) ^ 2 =
      ∑ i ∈ s, p i ^ 2 + ∑ i ∈ s, q i ^ 2 - 2 * ∑ i ∈ s, p i * q i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc √(∑ i ∈ s, (p i - q i) ^ 2)
      ≤ √((√(∑ i ∈ s, p i ^ 2) + √(∑ i ∈ s, q i ^ 2)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hexp, add_sq, Real.sq_sqrt hP, Real.sq_sqrt hQ]
        linarith [neg_abs_le (∑ i ∈ s, p i * q i)]
    _ = √(∑ i ∈ s, p i ^ 2) + √(∑ i ∈ s, q i ^ 2) := Real.sqrt_sq (by positivity)

/-! ### The Marcinkiewicz–Zygmund inequality -/

/-- Symmetrization identity: `𝔼 |∑ ε_r (U_r - U'_r)|` does not depend on the sign pattern,
so the expectation over `x` of `|∑ r, ε_r u (x r)|` is at most that of
`|∑ r, (u (x r) - u (y r))|` over the pair `(x, y)`. -/
theorem sum_prod_mul_abs_sum_ite_neg_le {α : Type*} [Fintype α] (M u : α → ℝ)
    (hM : ∀ a, 0 ≤ M a) (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) {k : ℕ}
    (ε : Fin k → Bool) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, (if ε r then u (x r) else -u (x r))| ≤
      ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) *
        |∑ r, (u (x r) - u (y r))| := by
  have hW : ∀ y : Fin k → α, 0 ≤ ∏ r, M (y r) := fun y => Finset.prod_nonneg fun r _ => hM _
  calc ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, (if ε r then u (x r) else -u (x r))|
      ≤ ∑ x : Fin k → α, (∏ r, M (x r)) * ∑ y : Fin k → α, (∏ r, M (y r)) *
          |∑ r, (if ε r then u (x r) - u (y r) else -(u (x r) - u (y r)))| :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (abs_sum_ite_neg_le_sum_prod_mul_abs M u hM hM1 hu ε x) (hW x)
    _ = ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) *
          |∑ r, (if ε r then u (x r) - u (y r) else -(u (x r) - u (y r)))| :=
        Finset.sum_congr rfl fun x _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
    _ = _ := sum_sum_prod_mul_abs_sum_ite_neg M u ε

/-- **Lower half of the Marcinkiewicz–Zygmund inequality**:
`𝔼 √(∑ r, U_r²) ≤ 2 √3 𝔼 |∑ r, U_r|` for independent centred `U_r = u (x r)`. -/
theorem sum_prod_mul_sqrt_le {α : Type*} [Fintype α] (M u : α → ℝ) (hM : ∀ a, 0 ≤ M a)
    (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) ≤
      2 * √3 * ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)| := by
  have hW : ∀ y : Fin k → α, 0 ≤ ∏ r, M (y r) := fun y => Finset.prod_nonneg fun r _ => hM _
  set D := ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) *
        |∑ r, (u (x r) - u (y r))| with hD
  have hDle : D ≤ 2 * ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)| := by
    rw [← sum_sum_prod_mul_add M hM1 fun x => |∑ r, u (x r)|]
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hW x) (hW y))
    rw [Finset.sum_sub_distrib]
    exact abs_sub _ _
  calc ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2)
      ≤ ∑ x : Fin k → α, (∏ r, M (x r)) *
          (√3 * ((∑ ε : Fin k → Bool, |∑ r, (if ε r then u (x r) else -u (x r))|) / 2 ^ k)) :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (sqrt_sum_sq_le_sqrt_three_mul fun r => u (x r)) (hW x)
    _ = √3 / 2 ^ k * ∑ x : Fin k → α, ∑ ε : Fin k → Bool,
          (∏ r, M (x r)) * |∑ r, (if ε r then u (x r) else -u (x r))| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.mul_sum]
        ring
    _ = √3 / 2 ^ k * ∑ ε : Fin k → Bool, ∑ x : Fin k → α,
          (∏ r, M (x r)) * |∑ r, (if ε r then u (x r) else -u (x r))| := by
        rw [Finset.sum_comm]
    _ ≤ √3 / 2 ^ k * ∑ _ε : Fin k → Bool, D := by
        gcongr with ε
        exact sum_prod_mul_abs_sum_ite_neg_le M u hM hM1 hu ε
    _ = √3 * D := by
        rw [sum_const_pi_fin_bool]
        field_simp
    _ ≤ √3 * (2 * ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)|) := by gcongr
    _ = 2 * √3 * ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)| := by ring

/-- **Upper half of the Marcinkiewicz–Zygmund inequality**:
`𝔼 |∑ r, U_r| ≤ 2 𝔼 √(∑ r, U_r²)` for independent centred `U_r = u (x r)`. -/
theorem sum_prod_mul_abs_le {α : Type*} [Fintype α] (M u : α → ℝ) (hM : ∀ a, 0 ≤ M a)
    (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) (k : ℕ) :
    ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)| ≤
      2 * ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) := by
  have hW : ∀ y : Fin k → α, 0 ≤ ∏ r, M (y r) := fun y => Finset.prod_nonneg fun r _ => hM _
  set D := ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) *
        |∑ r, (u (x r) - u (y r))| with hD
  -- Jensen in the copy, with all coefficients equal to one.
  have hJ : ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)| ≤ D :=
    calc ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)|
        ≤ ∑ x : Fin k → α, (∏ r, M (x r)) * ∑ y : Fin k → α, (∏ r, M (y r)) *
            |∑ r, (u (x r) - u (y r))| :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (abs_sum_le_sum_prod_mul_abs M u hM hM1 hu x) (hW x)
      _ = D := Finset.sum_congr rfl fun x _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
  -- Averaging the swap lemma over all sign patterns.
  have hsum : 2 ^ k * D = ∑ x : Fin k → α, ∑ y : Fin k → α,
      (∏ r, M (x r)) * (∏ r, M (y r)) *
        ∑ ε : Fin k → Bool, |∑ r, (if ε r then u (x r) - u (y r) else -(u (x r) - u (y r)))| := by
    calc 2 ^ k * D = ∑ ε : Fin k → Bool, ∑ x : Fin k → α, ∑ y : Fin k → α,
          (∏ r, M (x r)) * (∏ r, M (y r)) *
            |∑ r, (if ε r then u (x r) - u (y r) else -(u (x r) - u (y r)))| := by
          rw [Finset.sum_congr rfl fun ε _ => sum_sum_prod_mul_abs_sum_ite_neg M u ε,
            sum_const_pi_fin_bool]
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
  have hD' : D = ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) *
      ((∑ ε : Fin k → Bool,
        |∑ r, (if ε r then u (x r) - u (y r) else -(u (x r) - u (y r)))|) / 2 ^ k) := by
    simp only [mul_div_assoc', ← Finset.sum_div]
    rw [← hsum, mul_div_cancel_left₀ _ (by positivity)]
  calc ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)|
      ≤ D := hJ
    _ = _ := hD'
    _ ≤ ∑ x : Fin k → α, ∑ y : Fin k → α, (∏ r, M (x r)) * (∏ r, M (y r)) *
          (√(∑ r, u (x r) ^ 2) + √(∑ r, u (y r) ^ 2)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left
            ((khintchine_one fun r => u (x r) - u (y r)).2.trans
              (sqrt_sum_sub_sq_le Finset.univ (fun r => u (x r)) fun r => u (y r)))
            (mul_nonneg (hW x) (hW y))
    _ = 2 * ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) :=
        sum_sum_prod_mul_add M hM1 fun x => √(∑ r, u (x r) ^ 2)

/-- **The Marcinkiewicz–Zygmund inequality with exponent one.** Let `M` be a probability
weight on a finite type `α` and `u` centred under `M`. For `k` independent coordinates
`x r` of law `M`, put `U_r = u (x r)`. Then
`(1 / (2√3)) 𝔼 √(∑ r, U_r²) ≤ 𝔼 |∑ r, U_r| ≤ 2 𝔼 √(∑ r, U_r²)`. -/
theorem marcinkiewiczZygmund_one {α : Type} [Fintype α] (M u : α → ℝ) (hM : ∀ a, 0 ≤ M a)
    (hM1 : ∑ a, M a = 1) (hu : ∑ a, M a * u a = 0) (k : ℕ) :
    1 / (2 * √3) * ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) ≤
        ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)| ∧
      ∑ x : Fin k → α, (∏ r, M (x r)) * |∑ r, u (x r)| ≤
        2 * ∑ x : Fin k → α, (∏ r, M (x r)) * √(∑ r, u (x r) ^ 2) := by
  refine ⟨?_, sum_prod_mul_abs_le M u hM hM1 hu k⟩
  have h := sum_prod_mul_sqrt_le M u hM hM1 hu k
  have h3 : 0 < 2 * √3 := by positivity
  rw [one_div, inv_mul_le_iff₀ h3]
  exact h

end Parking
