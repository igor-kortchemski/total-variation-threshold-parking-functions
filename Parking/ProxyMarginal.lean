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

public import Parking.External
public import Parking.Marginal
public import Parking.ProxySums
import Parking.MarginalSquares

/-!
# The AKVZ proxy of the marginal law

This module proves the midpoint and score identities and the proxy comparison
used in `lem:products`, without assuming a citation interface.

* Formulas (`lem:products`). Since `μ_n(j) = (1 + g_n(j)) / n` and `U_n(j) = 1 / n`, the
  AKVZ score of `(μ_n, U_n)` is `u(j) = g_n(j) / (2 + g_n(j))` (`akvzScore_marginal_uniformLaw`)
  and the midpoint is `M(j) = (2 + g_n(j)) / (2n)`, so that the proxy is
  `Ψ(s) = ∑_j M(j) min (u(j)² / s², |u(j)| / s)` (`akvzProxy_marginal_uniformLaw`).
* First comparison (`lem:products`). Let `g` satisfy the conclusions of `lem:marginal`
  with constants `c, C, ε`, and let `s = √b` with `b = b_{n,k}`. Then `k Ψ(s)` lies between
  `min (c²/9, c/3) min (1, ε/2) / 8` and `18 max (C², C)` (`proxySum_bounds`). Write
  `m(t) = min (t² / s², |t| / s)`, monotone in `|t|`, and `φ(x) = min (1 / (b x), 1 / √(b x))`,
  antitone in `x > 0`, so that `m(1 / √x) = φ(x)` (`min_sq_div_one_div_sqrt`).
  * Upper bound (`proxySum_le`). `M(j) ≤ 3 / (2n)` and `|u(j)| ≤ |g(j)| ≤ C / √m_j`, with
    `m_j = min (j + 1, n - j)` (`0`-based `j`). Hence `m(u(j)) ≤ max (C², C) φ(m_j)`
    (`proxyTerm_le`), and `φ(m_j) ≤ φ(j + 1) + φ(n - j)`. The reflection `j ↦ n - 1 - j`
    (`sum_fin_reflect`) and the upper bound `6` of the split sum (`sum_min_inv_bScale_le`)
    conclude.
  * Lower bound (`le_proxySum`). On the initial range `j + 1 ≤ max (1, ⌊ε n⌋)`, `M(j) ≥ 1 / (2n)`
    and `u(j) ≥ g(j) / 3 ≥ c / (3 √(j + 1))`, so the summand is at least
    `min (c²/9, c/3) φ(j + 1) / (2n)` (`le_proxyTerm`). The other summands are nonnegative.
    Since `φ` is antitone, the average over `[0, N')`, with
    `N' = min (n, max (1, ⌊ε n⌋)) ≥ min (1, ε/2) n` (`min_one_half_mul_le_min_max_floor`),
    dominates the full average (`mul_sum_range_le_of_antitone`), and the lower bound `1/4` of
    the split sum (`le_sum_min_inv_bScale`) concludes.
* Instantiation (`exists_akvzProxy_marginal_comparable`). The constants of `parkingG_marginal`
  give `0 < c₁ ≤ k Ψ(√b_{n,k}) ≤ C₁` for all `n ≥ 2` and `1 ≤ k ≤ n`, with `c₁, C₁`
  independent of `n` and `k`.
-/

public section

namespace Parking

open Finset

/-! ### Formulas for the score and the proxy -/

/-- The mass of an atom under the uniform law on `Fin n`: `U_n(j) = 1 / n`. -/
theorem uniformLaw_fin_apply_singleton (n : ℕ+) (j : Fin n) :
    (uniformLaw (Fin n) {j} : ℝ) = 1 / n := by
  have h := uniformLaw_apply (α := Fin n) {j}
  rw [Finset.coe_singleton, Finset.card_singleton, Fintype.card_fin, Nat.cast_one] at h
  exact h

/-- The AKVZ score of `(μ_n, U_n)` (`lem:products`):
`u(j) = (μ_n(j) - 1/n) / (μ_n(j) + 1/n) = g_n(j) / (2 + g_n(j))`. -/
theorem akvzScore_marginal_uniformLaw (n : ℕ+) (j : Fin n) :
    akvzScore (marginal n) (uniformLaw (Fin n)) j = parkingG n j / (2 + parkingG n j) := by
  have hn : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 n.pos).ne'
  rw [akvzScore, marginal_apply_singleton_eq, uniformLaw_fin_apply_singleton, div_sub_div_same,
    ← add_div, div_div_div_cancel_right₀ hn]
  congr 1 <;> ring

/-- The AKVZ proxy of `(μ_n, U_n)` (`lem:products`): with midpoint
`M(j) = (μ_n(j) + 1/n) / 2 = (2 + g_n(j)) / (2n)` and score `u(j) = g_n(j) / (2 + g_n(j))`,
`Ψ(s) = ∑_j M(j) min (u(j)² / s², |u(j)| / s)`. -/
theorem akvzProxy_marginal_uniformLaw (n : ℕ+) (s : ℝ) :
    akvzProxy (marginal n) (uniformLaw (Fin n)) s =
      ∑ j, (2 + parkingG n j) / (2 * n) *
        min ((parkingG n j / (2 + parkingG n j)) ^ 2 / s ^ 2)
          (|parkingG n j / (2 + parkingG n j)| / s) := by
  unfold akvzProxy
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [akvzScore_marginal_uniformLaw, marginal_apply_singleton_eq, uniformLaw_fin_apply_singleton,
    ← add_div, div_div]
  congr 1
  rw [mul_comm (n : ℝ) 2]
  congr 1
  ring

/-! ### The truncated quadratic `m(t) = min (t² / s², |t| / s)` -/

/-- `m(t) = min (t² / s², |t| / s)` is nonnegative, for `s ≥ 0`. -/
theorem min_sq_div_nonneg {s : ℝ} (hs : 0 ≤ s) (t : ℝ) : 0 ≤ min (t ^ 2 / s ^ 2) (|t| / s) :=
  le_min (by positivity) (div_nonneg (abs_nonneg t) hs)

/-- `m(t) = min (t² / s², |t| / s)` is monotone in `|t|`, for `s ≥ 0`. -/
theorem min_sq_div_le_min_sq_div {s t t' : ℝ} (hs : 0 ≤ s) (h : |t| ≤ |t'|) :
    min (t ^ 2 / s ^ 2) (|t| / s) ≤ min (t' ^ 2 / s ^ 2) (|t'| / s) :=
  min_le_min (div_le_div_of_nonneg_right (sq_le_sq.2 h) (sq_nonneg s))
    (div_le_div_of_nonneg_right h hs)

/-- Upper scaling of `m(t) = min (t² / s², |t| / s)`: `m(a t) ≤ max (a², a) m(t)`, for
`a, s ≥ 0`. -/
theorem min_sq_div_mul_le {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (t : ℝ) :
    min ((a * t) ^ 2 / s ^ 2) (|a * t| / s) ≤ max (a ^ 2) a * min (t ^ 2 / s ^ 2) (|t| / s) := by
  rw [mul_min_of_nonneg _ _ (le_max_of_le_right ha), mul_pow, abs_mul, abs_of_nonneg ha,
    mul_div_assoc, mul_div_assoc]
  exact min_le_min (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (div_nonneg (abs_nonneg t) hs))

/-- Lower scaling of `m(t) = min (t² / s², |t| / s)`: `min (a², a) m(t) ≤ m(a t)`, for
`a, s ≥ 0`. -/
theorem le_min_sq_div_mul {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (t : ℝ) :
    min (a ^ 2) a * min (t ^ 2 / s ^ 2) (|t| / s) ≤ min ((a * t) ^ 2 / s ^ 2) (|a * t| / s) := by
  rw [mul_min_of_nonneg _ _ (le_min (sq_nonneg a) ha), mul_pow, abs_mul, abs_of_nonneg ha,
    mul_div_assoc, mul_div_assoc]
  exact min_le_min (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (div_nonneg (abs_nonneg t) hs))

/-- At `t = 1 / √x` and `s = √b`, with `b, x ≥ 0`:
`m(t) = min (t² / s², |t| / s) = min (1 / (b x), 1 / √(b x)) = φ(x)`. -/
theorem min_sq_div_one_div_sqrt {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) :
    min ((1 / √x) ^ 2 / √b ^ 2) (|1 / √x| / √b) = min (1 / (b * x)) (1 / √(b * x)) := by
  rw [div_pow, one_pow, Real.sq_sqrt hx, Real.sq_sqrt hb,
    abs_of_nonneg (one_div_nonneg.2 (Real.sqrt_nonneg x)), Real.sqrt_mul hb, div_div, div_div,
    mul_comm x b, mul_comm (√x) (√b)]

/-! ### The function `φ(x) = min (1 / (b x), 1 / √(b x))` -/

/-- `φ(x) = min (1 / (b x), 1 / √(b x))` is nonnegative, for `b, x ≥ 0`. -/
theorem min_inv_nonneg {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) :
    0 ≤ min (1 / (b * x)) (1 / √(b * x)) :=
  le_min (by positivity) (by positivity)

/-- `φ(x) = min (1 / (b x), 1 / √(b x))` is antitone in `x > 0`, for `b > 0`. -/
theorem min_inv_le_min_inv {b x y : ℝ} (hb : 0 < b) (hx : 0 < x) (hxy : x ≤ y) :
    min (1 / (b * y)) (1 / √(b * y)) ≤ min (1 / (b * x)) (1 / √(b * x)) := by
  have h₁ : 0 < b * x := mul_pos hb hx
  have h₂ : b * x ≤ b * y := mul_le_mul_of_nonneg_left hxy hb.le
  exact min_le_min (one_div_le_one_div_of_le h₁ h₂)
    (one_div_le_one_div_of_le (Real.sqrt_pos.2 h₁) (Real.sqrt_le_sqrt h₂))

/-! ### One summand of the proxy -/

/-- Upper bound of one summand of the proxy. If `1 ≤ 2 + g ≤ 3`, `|g| ≤ C / √x` with `C ≥ 0`
and `x > 0`, and `b ≥ 0`, `n > 0`, then, at `s = √b`,
`(2 + g) / (2n) · m(g / (2 + g)) ≤ 3 max (C², C) / (2n) · φ(x)`. -/
theorem proxyTerm_le {b n g C x : ℝ} (hb : 0 ≤ b) (hn : 0 < n) (hg₁ : 1 ≤ 2 + g)
    (hg₂ : 2 + g ≤ 3) (hC : 0 ≤ C) (hx : 0 < x) (hgC : |g| ≤ C / √x) :
    (2 + g) / (2 * n) * min ((g / (2 + g)) ^ 2 / √b ^ 2) (|g / (2 + g)| / √b) ≤
      3 * max (C ^ 2) C / (2 * n) * min (1 / (b * x)) (1 / √(b * x)) := by
  have hs : 0 ≤ √b := Real.sqrt_nonneg b
  have hu : |g / (2 + g)| ≤ |C * (1 / √x)| := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 + g), mul_one_div,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ C / √x)]
    exact (div_le_self (abs_nonneg g) hg₁).trans hgC
  have hm : min ((g / (2 + g)) ^ 2 / √b ^ 2) (|g / (2 + g)| / √b) ≤
      max (C ^ 2) C * min (1 / (b * x)) (1 / √(b * x)) :=
    calc _ ≤ min ((C * (1 / √x)) ^ 2 / √b ^ 2) (|C * (1 / √x)| / √b) :=
          min_sq_div_le_min_sq_div hs hu
      _ ≤ max (C ^ 2) C * min ((1 / √x) ^ 2 / √b ^ 2) (|1 / √x| / √b) :=
          min_sq_div_mul_le hs hC _
      _ = max (C ^ 2) C * min (1 / (b * x)) (1 / √(b * x)) := by
          rw [min_sq_div_one_div_sqrt hb hx.le]
  calc _ ≤ 3 / (2 * n) * (max (C ^ 2) C * min (1 / (b * x)) (1 / √(b * x))) :=
        mul_le_mul (div_le_div_of_nonneg_right hg₂ (by positivity)) hm
          (min_sq_div_nonneg hs _) (by positivity)
    _ = 3 * max (C ^ 2) C / (2 * n) * min (1 / (b * x)) (1 / √(b * x)) := by ring

/-- Lower bound of one summand of the proxy. If `g ≤ 1` and `c / √x ≤ g` with `c ≥ 0` and
`x > 0`, and `b ≥ 0`, `n > 0`, then, at `s = √b`,
`min (c²/9, c/3) / (2n) · φ(x) ≤ (2 + g) / (2n) · m(g / (2 + g))`. -/
theorem le_proxyTerm {b n g c x : ℝ} (hb : 0 ≤ b) (hn : 0 < n) (hg₂ : g ≤ 1) (hc : 0 ≤ c)
    (hx : 0 < x) (hcg : c / √x ≤ g) :
    min (c ^ 2 / 9) (c / 3) / (2 * n) * min (1 / (b * x)) (1 / √(b * x)) ≤
      (2 + g) / (2 * n) * min ((g / (2 + g)) ^ 2 / √b ^ 2) (|g / (2 + g)| / √b) := by
  have hs : 0 ≤ √b := Real.sqrt_nonneg b
  have hg₀ : 0 ≤ g := (by positivity : (0 : ℝ) ≤ c / √x).trans hcg
  have h2g : 0 < 2 + g := by linarith
  have hu : |c / 3 * (1 / √x)| ≤ |g / (2 + g)| := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ c / 3 * (1 / √x)),
      abs_of_nonneg (div_nonneg hg₀ h2g.le)]
    calc c / 3 * (1 / √x) = c / √x / 3 := by ring
      _ ≤ g / 3 := div_le_div_of_nonneg_right hcg (by norm_num)
      _ ≤ g / (2 + g) := div_le_div_of_nonneg_left hg₀ h2g (by linarith)
  have hm : min (c ^ 2 / 9) (c / 3) * min (1 / (b * x)) (1 / √(b * x)) ≤
      min ((g / (2 + g)) ^ 2 / √b ^ 2) (|g / (2 + g)| / √b) :=
    calc _ = min ((c / 3) ^ 2) (c / 3) * min ((1 / √x) ^ 2 / √b ^ 2) (|1 / √x| / √b) := by
          rw [min_sq_div_one_div_sqrt hb hx.le, div_pow]
          norm_num
      _ ≤ min ((c / 3 * (1 / √x)) ^ 2 / √b ^ 2) (|c / 3 * (1 / √x)| / √b) :=
          le_min_sq_div_mul hs (by positivity) _
      _ ≤ _ := min_sq_div_le_min_sq_div hs hu
  calc _ = 1 / (2 * n) * (min (c ^ 2 / 9) (c / 3) * min (1 / (b * x)) (1 / √(b * x))) := by
        ring
    _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right (by linarith) (by positivity)) hm
          (by positivity) (by positivity)

/-! ### The initial range of `lem:marginal` -/

/-- The initial range of `lem:marginal` is a positive proportion of `[0, n)`:
`min (1, ε/2) n ≤ min (n, max (1, ⌊ε n⌋))`. -/
theorem min_one_half_mul_le_min_max_floor (ε : ℝ) (n : ℕ) :
    min 1 (ε / 2) * n ≤ ((min n (max 1 ⌊ε * (n : ℝ)⌋₊) : ℕ) : ℝ) := by
  rw [Nat.cast_min, Nat.cast_max, Nat.cast_one]
  have hm : min 1 (ε / 2) * n ≤ ε / 2 * n :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
  refine le_min (mul_le_of_le_one_left (by positivity) (min_le_left _ _)) ?_
  rcases lt_or_ge (ε * n) 2 with h | h
  · exact le_max_of_le_left (by linarith)
  · have hfl := Nat.lt_floor_add_one (ε * n)
    exact le_max_of_le_right (by linarith)

/-! ### The first comparison -/

/-- Upper half of `proxySum_bounds`: under the upper bounds of `lem:marginal`,
`k Ψ(√b_{n,k}) ≤ 18 max (C², C)`. -/
theorem proxySum_le {C : ℝ} (hC : 0 ≤ C) (n : ℕ+) (g : Fin n → ℝ)
    (hg : ∀ j : Fin n, Real.exp (-1) ≤ 1 + g j ∧ 1 + g j ≤ 2 ∧
      |g j| ≤ C / √((min ((j : ℕ) + 1) ((n : ℕ) - j) : ℕ) : ℝ))
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (k : ℝ) * ∑ j, (2 + g j) / (2 * n) *
        min ((g j / (2 + g j)) ^ 2 / √(bScale n k) ^ 2) (|g j / (2 + g j)| / √(bScale n k)) ≤
      18 * max (C ^ 2) C := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 n.pos
  have hb : 0 < bScale n k := bScale_pos n.pos hk
  let f : ℕ → ℝ := fun i => min (1 / (bScale n k * i)) (1 / √(bScale n k * i))
  have hf₀ : ∀ i, 0 ≤ f i := fun i => min_inv_nonneg hb.le (Nat.cast_nonneg i)
  have hterm : ∀ j : Fin n, (2 + g j) / (2 * n) *
      min ((g j / (2 + g j)) ^ 2 / √(bScale n k) ^ 2) (|g j / (2 + g j)| / √(bScale n k)) ≤
      3 * max (C ^ 2) C / (2 * n) * (f ((j : ℕ) + 1) + f ((n : ℕ) - j)) := by
    intro j
    obtain ⟨h₁, h₂, h₃⟩ := hg j
    have hj := j.isLt
    have hm : 1 ≤ min ((j : ℕ) + 1) ((n : ℕ) - j) := le_min (by omega) (by omega)
    refine (proxyTerm_le hb.le hnR (by linarith [Real.exp_pos (-1)]) (by linarith) hC
      (by exact_mod_cast hm) h₃).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rcases le_total ((j : ℕ) + 1) ((n : ℕ) - j) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (hf₀ _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (hf₀ _)
  have hsum : ∑ j : Fin n, f ((n : ℕ) - j) = ∑ j : Fin n, f ((j : ℕ) + 1) := sum_fin_reflect f
  have hP2 : (k : ℝ) / n * ∑ j : Fin n, f ((j : ℕ) + 1) ≤ 6 := by
    have hfj : ∀ j : Fin n, f ((j : ℕ) + 1) =
        min (1 / (bScale n k * ((j : ℝ) + 1))) (1 / √(bScale n k * ((j : ℝ) + 1))) := by
      intro j
      simp only [f, Nat.cast_add, Nat.cast_one]
    rw [sum_congr rfl fun j _ => hfj j]
    exact sum_min_inv_bScale_le n k hk hkn
  calc _ ≤ (k : ℝ) * ∑ j : Fin n,
        3 * max (C ^ 2) C / (2 * n) * (f ((j : ℕ) + 1) + f ((n : ℕ) - j)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hterm j) (Nat.cast_nonneg k)
    _ = 3 * max (C ^ 2) C * ((k : ℝ) / n * ∑ j : Fin n, f ((j : ℕ) + 1)) := by
        rw [← mul_sum, sum_add_distrib, hsum]
        ring
    _ ≤ 3 * max (C ^ 2) C * 6 := mul_le_mul_of_nonneg_left hP2 (by positivity)
    _ = 18 * max (C ^ 2) C := by ring

/-- A sum over the initial range `[0, N)`, with `N ≤ n`, is at most a sum over `Fin n` of
nonnegative terms that dominate it termwise on that range. -/
theorem sum_range_le_sum_fin {n N : ℕ} (hNn : N ≤ n) {f : ℕ → ℝ} {F : Fin n → ℝ}
    (hF₀ : ∀ j, 0 ≤ F j) (hF : ∀ j : Fin n, (j : ℕ) < N → f j ≤ F j) :
    ∑ i ∈ range N, f i ≤ ∑ j, F j :=
  calc ∑ i ∈ range N, f i = ∑ i : Fin N, f i := (Fin.sum_univ_eq_sum_range f N).symm
    _ ≤ ∑ i : Fin N, F (Fin.castLEEmb hNn i) :=
        sum_le_sum fun i _ => hF (Fin.castLEEmb hNn i) i.isLt
    _ = ∑ j ∈ univ.map (Fin.castLEEmb hNn), F j := (sum_map _ _ _).symm
    _ ≤ ∑ j, F j := sum_le_univ_sum_of_nonneg hF₀

/-- Averaging step of the lower bound of `proxySum_bounds`. Let `f : ℕ → ℝ` be antitone and
`F : Fin n → ℝ` nonnegative, with `K / (2n) · f j ≤ F j` for `j < N`, where `N ≤ n` and
`m n ≤ N`. If `1/4 ≤ (k / n) ∑_{i < n} f i`, then `K m / 8 ≤ k ∑_j F j`. -/
theorem le_mul_sum_of_initial_range {n N : ℕ} (hNn : N ≤ n) (hn : 0 < n) {K m k : ℝ}
    (hK : 0 ≤ K) (hk : 0 ≤ k) {f : ℕ → ℝ} (hf : Antitone f) {F : Fin n → ℝ}
    (hF₀ : ∀ j, 0 ≤ F j) (hF : ∀ j : Fin n, (j : ℕ) < N → K / (2 * n) * f j ≤ F j)
    (hm : m * n ≤ N) (hP : 1 / 4 ≤ k / n * ∑ i ∈ range n, f i) :
    K * m / 8 ≤ k * ∑ j, F j := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hn₀ : (n : ℝ) ≠ 0 := hnR.ne'
  have hsub : K / (2 * n) * ∑ i ∈ range N, f i ≤ ∑ j, F j := by
    rw [mul_sum]
    exact sum_range_le_sum_fin (f := fun i => K / (2 * n) * f i) hNn hF₀ hF
  have hav := mul_sum_range_le_of_antitone hf hNn
  calc K * m / 8 = K * m / 8 * n / n := (mul_div_cancel_right₀ _ hn₀).symm
    _ = K / (2 * n) * (m * n) * (1 / 4) := by ring
    _ ≤ K / (2 * n) * N * (k / n * ∑ i ∈ range n, f i) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hP (by norm_num)
          (by positivity)
    _ = k * (K / (2 * n)) * ((N : ℝ) * ∑ i ∈ range n, f i) / n := by ring
    _ ≤ k * (K / (2 * n)) * ((n : ℝ) * ∑ i ∈ range N, f i) / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hav (by positivity)) hnR.le
    _ = k * (K / (2 * n) * ∑ i ∈ range N, f i) * n / n := by ring
    _ = k * (K / (2 * n) * ∑ i ∈ range N, f i) := mul_div_cancel_right₀ _ hn₀
    _ ≤ k * ∑ j, F j := mul_le_mul_of_nonneg_left hsub hk

/-- Lower half of `proxySum_bounds`: under the bounds `e^{-1} ≤ 1 + g ≤ 2` and the lower
bound of `lem:marginal` on the initial range,
`min (c²/9, c/3) min (1, ε/2) / 8 ≤ k Ψ(√b_{n,k})`. No sign condition on `ε` is needed: for
`ε ≤ 0` the left-hand side is nonpositive. -/
theorem le_proxySum {c ε : ℝ} (hc : 0 ≤ c) (n : ℕ+) (g : Fin n → ℝ)
    (hg : ∀ j : Fin n, Real.exp (-1) ≤ 1 + g j ∧ 1 + g j ≤ 2)
    (hlow : ∀ j : Fin n, (j : ℕ) + 1 ≤ max 1 ⌊ε * (n : ℝ)⌋₊ → c / √((j : ℝ) + 1) ≤ g j)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    min (c ^ 2 / 9) (c / 3) * min 1 (ε / 2) / 8 ≤
      (k : ℝ) * ∑ j, (2 + g j) / (2 * n) *
        min ((g j / (2 + g j)) ^ 2 / √(bScale n k) ^ 2) (|g j / (2 + g j)| / √(bScale n k)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 n.pos
  have hb : 0 < bScale n k := bScale_pos n.pos hk
  refine le_mul_sum_of_initial_range (N := min (n : ℕ) (max 1 ⌊ε * (n : ℝ)⌋₊))
    (f := fun i => min (1 / (bScale n k * ((i : ℝ) + 1))) (1 / √(bScale n k * ((i : ℝ) + 1))))
    (min_le_left _ _) n.pos (le_min (by positivity) (by positivity)) (Nat.cast_nonneg k)
    (fun i i' h => min_inv_le_min_inv hb (by positivity)
      (by exact_mod_cast Nat.add_le_add_right h 1))
    (fun j => mul_nonneg (div_nonneg (by linarith [(hg j).1, Real.exp_pos (-1)]) (by positivity))
      (min_sq_div_nonneg (Real.sqrt_nonneg _) _))
    (fun j hj => le_proxyTerm hb.le hnR (by linarith [(hg j).2]) hc (by positivity)
      (hlow j (Nat.succ_le_of_lt (hj.trans_le (min_le_right _ _)))))
    (min_one_half_mul_le_min_max_floor ε n) ?_
  rw [← Fin.sum_univ_eq_sum_range]
  exact le_sum_min_inv_bScale n k hk hkn

/-- Proxy comparison (`lem:products`). Let `g : Fin n → ℝ` satisfy the
conclusions of `lem:marginal` (`parkingG_marginal`) with constants `c, C > 0` and `ε`, and let
`1 ≤ k ≤ n`. Then, at `s = √b_{n,k}`,
`min (c²/9, c/3) min (1, ε/2) / 8 ≤ k ∑_j (2 + g j) / (2n) min (u_j² / s², |u_j| / s) ≤
18 max (C², C)`, with `u_j = g j / (2 + g j)`. No sign condition on `ε` is needed: for
`ε ≤ 0` the lower bound is nonpositive. -/
theorem proxySum_bounds {c C ε : ℝ} (hc : 0 < c) (hC : 0 < C) (n : ℕ+)
    (g : Fin n → ℝ)
    (hg : ∀ j : Fin n, Real.exp (-1) ≤ 1 + g j ∧ 1 + g j ≤ 2 ∧
      |g j| ≤ C / √((min ((j : ℕ) + 1) ((n : ℕ) - j) : ℕ) : ℝ))
    (hlow : ∀ j : Fin n, (j : ℕ) + 1 ≤ max 1 ⌊ε * (n : ℝ)⌋₊ → c / √((j : ℝ) + 1) ≤ g j)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    min (c ^ 2 / 9) (c / 3) * min 1 (ε / 2) / 8 ≤
        (k : ℝ) * ∑ j, (2 + g j) / (2 * n) *
          min ((g j / (2 + g j)) ^ 2 / √(bScale n k) ^ 2) (|g j / (2 + g j)| / √(bScale n k)) ∧
      (k : ℝ) * ∑ j, (2 + g j) / (2 * n) *
          min ((g j / (2 + g j)) ^ 2 / √(bScale n k) ^ 2) (|g j / (2 + g j)| / √(bScale n k)) ≤
        18 * max (C ^ 2) C :=
  ⟨le_proxySum hc.le n g (fun j => ⟨(hg j).1, (hg j).2.1⟩) hlow k hk hkn,
    proxySum_le hC.le n g hg k hk hkn⟩

/-- Midpoint and score identities and Proxy comparison for the marginal law: there are
constants `0 < c₁ ≤ C₁` such that, for all `n ≥ 2` and `1 ≤ k ≤ n`, the AKVZ proxy of
`(μ_n, U_n)` at `s = √b_{n,k}` satisfies `c₁ ≤ k Ψ(s) ≤ C₁` (`lem:products`). -/
theorem exists_akvzProxy_marginal_comparable :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ c₁ ≤ C₁ ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) → ∀ k : ℕ, 1 ≤ k → k ≤ n →
      c₁ ≤ k * akvzProxy (marginal n) (uniformLaw (Fin n)) √(bScale n k) ∧
        k * akvzProxy (marginal n) (uniformLaw (Fin n)) √(bScale n k) ≤ C₁ := by
  obtain ⟨-, c, C, ε, hc, hC, hε, h⟩ := parkingG_marginal
  refine ⟨min (c ^ 2 / 9) (c / 3) * min 1 (ε / 2) / 8,
    max (min (c ^ 2 / 9) (c / 3) * min 1 (ε / 2) / 8) (18 * max (C ^ 2) C),
    by positivity, le_max_left _ _, fun n hn k hk hkn => ?_⟩
  obtain ⟨hg, hlow, -, -⟩ := h n hn
  rw [akvzProxy_marginal_uniformLaw]
  obtain ⟨h₁, h₂⟩ := proxySum_bounds hc hC n (parkingG n) hg hlow k hk hkn
  exact ⟨h₁, h₂.trans (le_max_right _ _)⟩

end Parking

end
