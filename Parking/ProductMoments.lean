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

public import Parking.CountPoly
public import Parking.Paper.Lorentzian
public import Parking.External
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Parking.PrefixLaw
import Parking.WordLaw
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Product moments of the first coordinates of a uniform parking function

The source is `lem:occupation_logconcavity`, which prove the product-moment
inequality (`eq:product_moments`)
`E_n[∏_{r ≤ k} z_{π_n(r)}] ≤ (∑_j μ_n(j) z_j)^k` by [LS26, inequality (3.6)].

* `expectedCount`: the expected counts `v_a = E_ν[#{j | ω_j = a}]` of a law `ν` on `[d]^m`.
* `eval_countPoly`: `h_ν(x) = ∑_ω ν(ω) ∏_j x_{ω_j}`.
* `eval_countPoly_le_of_lorentzian`: the source interface for [LS26, inequality (3.6)],
  used by the parking product-moment theorem after Lorentzian prefix closure. Its internal
  analytic proof is `eval_countPoly_le_of_completelyLogConcave`, under complete
  log-concavity, `h_ν(x) ≤ ((1 / m) ∑_a v_a x_a)^m` on the open positive orthant. The
  logarithm of `h_ν` is concave on the orthant, `h_ν(1) = 1`, the derivative of `h_ν` at `1`
  in the direction `u` is `∑_a v_a u_a`, and `∑_a v_a = m`. The tangent-line inequality at
  `1`, applied at `t x` with `t = m / ∑_a v_a x_a`, gives `h_ν(t x) ≤ 1`, and `h_ν` is
  homogeneous of degree `m`.
* `expectedCount_firstCoordsLaw`: by exchangeability, the expected number of occurrences of
  `j` among the first `k` coordinates of a uniform parking function is `k μ_n(j)`.
* `eval_countPoly_firstCoordsLaw_le`: conditional on the citation interface `BH20.SupportGenFunCLC`
  (`BH20.SupportGenFunCLC`), the product-moment inequality (`eq:product_moments`).

The parking-law consequences use the citation interface `BH20.SupportGenFunCLC`;
the general closure lemmas do not assume it.
-/

public section

open MeasureTheory MvPolynomial

namespace Parking

/-! ### Tangent-line inequality along a segment -/

/-- Tangent-line inequality along a segment: if `F` is concave on a set `S` containing `p`
and `q`, and `s ↦ F ((1 - s) • p + s • q)` has derivative `D` at `s = 0`, then
`F q ≤ F p + D`. -/
theorem le_add_of_concaveOn_of_hasDerivAt_lineMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {F : E → ℝ} (hF : ConcaveOn ℝ S F) {p q : E} (hp : p ∈ S) (hq : q ∈ S)
    {D : ℝ} (hD : HasDerivAt (fun s : ℝ => F (AffineMap.lineMap p q s)) D 0) :
    F q ≤ F p + D := by
  have h := (hF.comp_affineMap (AffineMap.lineMap p q)).slope_le_of_hasDerivAt
    (x := 0) (y := 1)
    (by simpa only [Set.mem_preimage, AffineMap.lineMap_apply_zero] using hp)
    (by simpa only [Set.mem_preimage, AffineMap.lineMap_apply_one] using hq) zero_lt_one hD
  rw [slope_def_field] at h
  simp only [Function.comp_apply, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, div_one] at h
  linarith

/-! ### Expected counts and the count-generating polynomial -/

/-- The expected counts `v_a = E_ν[#{j | ω_j = a}]` of a law `ν` on `[d]^m`
([LS26, §3.2]; `lem:occupation_logconcavity`). -/
@[expose] noncomputable def expectedCount {m d : ℕ} (ν : Measure (Fin m → Fin d)) (a : Fin d) :
    ℝ :=
  ∑ ω, ν.real {ω} * (Finset.univ.filter fun j => ω j = a).card

/-- The count-generating polynomial evaluated at `x`: `h_ν(x) = ∑_ω ν(ω) ∏_j x_{ω_j}`. -/
theorem eval_countPoly {m d : ℕ} (ν : Measure (Fin m → Fin d)) (x : Fin d → ℝ) :
    eval x (countPoly ν) = ∑ ω, ν.real {ω} * ∏ j, x (ω j) := by
  simp only [countPoly, map_sum, smul_eval, eval_prod, eval_X]

/-- `h_ν` is homogeneous of degree `m`: `h_ν(t x) = t^m h_ν(x)`. -/
theorem eval_countPoly_smul {m d : ℕ} (ν : Measure (Fin m → Fin d)) (t : ℝ)
    (x : Fin d → ℝ) : eval (t • x) (countPoly ν) = t ^ m * eval x (countPoly ν) := by
  simp only [eval_countPoly, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- For a probability law, `h_ν(1, …, 1) = 1`. -/
theorem eval_one_countPoly {m d : ℕ} (ν : Measure (Fin m → Fin d)) [IsProbabilityMeasure ν] :
    eval 1 (countPoly ν) = 1 := by
  simp only [eval_countPoly, Pi.one_apply, Finset.prod_const_one, mul_one,
    sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

/-- The expected counts are nonnegative. -/
theorem expectedCount_nonneg {m d : ℕ} (ν : Measure (Fin m → Fin d)) (a : Fin d) :
    0 ≤ expectedCount ν a :=
  Finset.sum_nonneg fun _ _ => mul_nonneg measureReal_nonneg (Nat.cast_nonneg _)

/-- `∑_a v_a g_a = E_ν[∑_j g_{ω_j}]`. -/
theorem sum_expectedCount_mul {m d : ℕ} (ν : Measure (Fin m → Fin d)) (g : Fin d → ℝ) :
    ∑ a, expectedCount ν a * g a = ∑ ω, ν.real {ω} * ∑ j, g (ω j) := by
  have key (ω : Fin m → Fin d) :
      ∑ j, g (ω j) = ∑ a, ((Finset.univ.filter fun j => ω j = a).card : ℝ) * g a := by
    rw [← Finset.sum_fiberwise Finset.univ ω (fun j => g (ω j))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_congr rfl fun j hj => congrArg g (Finset.mem_filter.1 hj).2,
      Finset.sum_const, nsmul_eq_mul]
  simp only [expectedCount, Finset.sum_mul, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun a _ => by ring

/-- For a probability law on `[d]^m`, `∑_a v_a = m`. -/
theorem sum_expectedCount {m d : ℕ} (ν : Measure (Fin m → Fin d)) [IsProbabilityMeasure ν] :
    ∑ a, expectedCount ν a = m := by
  calc ∑ a, expectedCount ν a = ∑ a, expectedCount ν a * 1 := by simp only [mul_one]
    _ = ∑ ω, ν.real {ω} * ∑ _j : Fin m, (1 : ℝ) := sum_expectedCount_mul ν fun _ => 1
    _ = m := by
      rw [← Finset.sum_mul, sum_measureReal_singleton, Finset.coe_univ, probReal_univ,
        one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The derivative of `h_ν` at `1` in the direction `y - 1` is `∑_a v_a (y_a - 1)`. -/
theorem hasDerivAt_eval_countPoly_lineMap {m d : ℕ} (ν : Measure (Fin m → Fin d))
    (y : Fin d → ℝ) :
    HasDerivAt (fun s : ℝ => eval (AffineMap.lineMap 1 y s) (countPoly ν))
      (∑ a, expectedCount ν a * (y a - 1)) 0 := by
  have hline (s : ℝ) (a : Fin d) :
      (AffineMap.lineMap (1 : Fin d → ℝ) y s) a = 1 + s * (y a - 1) := by
    simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.one_apply]
    ring
  have hfun : (fun s : ℝ => eval (AffineMap.lineMap 1 y s) (countPoly ν)) =
      fun s => ∑ ω, ν.real {ω} * ∏ j, (1 + s * (y (ω j) - 1)) := by
    funext s
    simp only [eval_countPoly, hline]
  rw [hfun, sum_expectedCount_mul]
  refine HasDerivAt.fun_sum fun ω _ => HasDerivAt.const_mul _ ?_
  have hprod := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun j s => 1 + s * (y (ω j) - 1)) (f' := fun j => y (ω j) - 1) (x := 0)
    fun j _ => by
      simpa only [hasDerivAt_const_add_iff, id_eq, one_mul] using
        ((hasDerivAt_id (0 : ℝ)).mul_const (y (ω j) - 1)).const_add 1
  convert hprod using 1
  simp only [zero_mul, add_zero, Finset.prod_const_one, smul_eq_mul, one_mul]

/-! ### Inequality (3.6) of Lee and Seo -/

/-- [LS26, inequality (3.6)] under complete log-concavity: for a law `ν` on `[d]^m` with
`m ≥ 1` whose count-generating polynomial is completely log-concave, and `x` in the open
positive orthant, `h_ν(x) ≤ ((1 / m) ∑_a v_a x_a)^m` (`lem:occupation_logconcavity`). Under complete log-concavity the logarithm of `h_ν` is concave on the
orthant (the empty list of directions in `CompletelyLogConcave`); the tangent-line
inequality at `1`, applied at `t x` with `t = m / ∑_a v_a x_a`, and the homogeneity of
`h_ν` give the bound. -/
theorem eval_countPoly_le_of_completelyLogConcave {m d : ℕ} (hm : 1 ≤ m)
    (ν : Measure (Fin m → Fin d)) [IsProbabilityMeasure ν]
    (h : CompletelyLogConcave (countPoly ν)) (x : Fin d → ℝ) (hx : ∀ a, 0 < x a) :
    eval x (countPoly ν) ≤ ((1 / (m : ℝ)) * ∑ a, expectedCount ν a * x a) ^ m := by
  set S := ∑ a, expectedCount ν a * x a with hS
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : ∑ a, expectedCount ν a = m := sum_expectedCount ν
  have hS0 : 0 < S := by
    obtain ⟨a, ha⟩ : ∃ a, 0 < expectedCount ν a := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : ∑ a, expectedCount ν a ≤ 0 := Finset.sum_nonpos fun a _ => hcon a
      linarith
    exact Finset.sum_pos' (fun b _ => mul_nonneg (expectedCount_nonneg ν b) (hx b).le)
      ⟨a, Finset.mem_univ a, mul_pos ha (hx a)⟩
  set t : ℝ := m / S with ht
  have ht0 : 0 < t := div_pos hm0 hS0
  have hyo : t • x ∈ posOrthant d := fun a => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos ht0 (hx a)
  have hone : (1 : Fin d → ℝ) ∈ posOrthant d := fun a => by
    simp only [Pi.one_apply, zero_lt_one]
  have h1 : eval 1 (countPoly ν) = 1 := eval_one_countPoly ν
  have hne : countPoly ν ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hconc : ConcaveOn ℝ (posOrthant d) fun z => Real.log (eval z (countPoly ν)) := by
    rcases h.2 [] (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]) with h0 | hc
    · simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at h0
      exact absurd h0 hne
    · simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using hc
  have hD := (hasDerivAt_eval_countPoly_lineMap ν (t • x)).log (by
    simp only [AffineMap.lineMap_apply_zero, h1]
    exact one_ne_zero)
  have htan := le_add_of_concaveOn_of_hasDerivAt_lineMap hconc hone hyo hD
  have hDval : ∑ a, expectedCount ν a * ((t • x) a - 1) = 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_one, Finset.sum_sub_distrib, hsum]
    have : ∑ a, expectedCount ν a * (t * x a) = t * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, ht, div_mul_cancel₀ _ hS0.ne', sub_self]
  simp only [AffineMap.lineMap_apply_zero, h1, Real.log_one, hDval, zero_div,
    add_zero] at htan
  have hpos : 0 < eval (t • x) (countPoly ν) := eval_pos_of_coeff_nonneg h.1 hne hyo
  have hle : t ^ m * eval x (countPoly ν) ≤ 1 := by
    rw [← eval_countPoly_smul]
    exact (Real.log_nonpos_iff hpos.le).1 htan
  have htm : 0 < t ^ m := pow_pos ht0 m
  have hinv : (1 / (m : ℝ)) * S = t⁻¹ := by
    rw [ht, inv_div]
    ring
  rw [hinv, inv_pow, ← one_div, le_div_iff₀ htm, mul_comm]
  exact hle

/-- [LS26, inequality (3.6)] for the genuine Lorentzian count polynomial.
The internally proved Lorentzian-to-complete implication supplies the analytic
tangent-line proof. -/
theorem eval_countPoly_le_of_lorentzian {m d : ℕ} (hm : 1 ≤ m)
    (ν : Measure (Fin m → Fin d)) [IsProbabilityMeasure ν]
    (h : Lorentzian m (countPoly ν)) (x : Fin d → ℝ) (hx : ∀ a, 0 < x a) :
    eval x (countPoly ν) ≤ ((1 / (m : ℝ)) * ∑ a, expectedCount ν a * x a) ^ m :=
  eval_countPoly_le_of_completelyLogConcave hm ν h.completelyLogConcave x hx

/-- [LS26, inequality (3.6)] with the manuscript's strong-log-concavity hypothesis.
The previously proved homogeneous equivalence supplies the complete-log-concavity
interface used internally by the tangent-line argument. -/
theorem eval_countPoly_le_of_stronglyLogConcave {m d : ℕ} (hm : 1 ≤ m)
    (ν : Measure (Fin m → Fin d)) [IsProbabilityMeasure ν]
    (h : StronglyLogConcave (countPoly ν)) (x : Fin d → ℝ) (hx : ∀ a, 0 < x a) :
    eval x (countPoly ν) ≤ ((1 / (m : ℝ)) * ∑ a, expectedCount ν a * x a) ^ m :=
  eval_countPoly_le_of_lorentzian hm ν
    (h.lorentzian (isHomogeneous_countPoly ν)) x hx

/-! ### The product-moment inequality -/

/-- By exchangeability, the expected number of occurrences of `j` among the first `k`
coordinates of a uniform parking function is `k μ_n(j)` (`lem:occupation_logconcavity`). -/
theorem expectedCount_firstCoordsLaw (n : ℕ+) (k : ℕ) (hk : k ≤ n) (j : Fin n) :
    expectedCount (firstCoordsLaw n k hk : Measure (Fin k → Fin n)) j =
      k * (marginal n {j} : ℝ) := by
  set ν := (firstCoordsLaw n k hk : Measure (Fin k → Fin n)) with hν
  have hcoord (r : Fin k) : ν.real {ω | ω r = j} = (marginal n {j} : ℝ) := by
    have hmap : ν.map (fun ω => ω r) = (marginal n : Measure (Fin n)) := by
      rw [marginal_eq_coordMarginalLaw n (Fin.castLE hk r), coordMarginalLaw, hν,
        firstCoordsLaw_eq_coordLaw, coordLaw,
        Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
      rfl
    rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, ← hmap,
      map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton j)]
    rfl
  have hsum : expectedCount ν j = ∑ r : Fin k, ν.real {ω | ω r = j} := by
    simp only [expectedCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_filter, sum_measureReal_singleton]
    congr 1
    ext ω
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  rw [hsum, Finset.sum_congr rfl fun r _ => hcoord r, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- Conditional on the citation interface `BH20.SupportGenFunCLC`, the
product-moment inequality (`eq:product_moments`, `lem:occupation_logconcavity`,
proved on `lem:occupation_logconcavity`): for `1 ≤ k ≤ n` and `z` in the open positive orthant,
`E_n[∏_{r ≤ k} z_{π_n(r)}] ≤ (∑_j μ_n(j) z_j)^k`. -/
theorem eval_countPoly_firstCoordsLaw_le (hBH : BH20.SupportGenFunCLC) (n : ℕ+) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k ≤ n) (z : Fin n → ℝ) (hz : ∀ j, 0 < z j) :
    eval z (countPoly (firstCoordsLaw n k hk : Measure (Fin k → Fin n))) ≤
      (∑ j, (marginal n {j} : ℝ) * z j) ^ k := by
  have h := eval_countPoly_le_of_lorentzian hk1 _
    (lorentzian_countPoly_firstCoordsLaw hBH n k hk) z hz
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk1
    exact this.ne'
  simp only [expectedCount_firstCoordsLaw] at h
  convert h using 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

end Parking

end
