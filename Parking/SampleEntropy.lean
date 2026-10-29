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

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Parking.CountPoly
public import Parking.Paper.Lorentzian
public import Parking.Entropy
public import Parking.Exchangeable
public import Parking.LogConcave
import Parking.EntropyKL
import Parking.PrefixLaw
import Parking.SequenceLemma
import Parking.StrongHan
import Parking.Paper.StrongCompleteEquivalence

/-!
# Relative entropy of the initial segments of an exchangeable law

`lem:sample_entropy` of `lem:sample_entropy`: for an exchangeable probability law `L` on `[d]^N`, `N ≥ 2`, whose coordinates all
have law `μ` and whose count-generating polynomial is strongly log-concave, the law of
the first `k` coordinates satisfies, for `1 ≤ k ≤ N`,
`KL(L(Z_1, …, Z_k) ‖ μ^{⊗k}) ≤ k(k-1)/(N(N-1)) · KL(L ‖ μ^{⊗N})`.

The manuscript invokes [LS26, Lemmas 3.4(1) and 3.7]. The proved homogeneous
strong/Lorentzian equivalence connects its hypothesis to Lorentzian prefix closure
and the deletion-sum theorem `strongHan_of_lorentzian`.

* `coordMarginalLaw_coordLaw`: the coordinates of an initial segment are coordinates of
  the whole word.
* `klDiv_coordLaw_pi_eq_entropy` (`lem:sample_entropy`): `D_m = m H_1 - H_m`, where
  `H_m = H(Z_1, …, Z_m)` and `D_m = KL(L(Z_1, …, Z_m) ‖ μ^{⊗m})`.
* `entropy_coordLaw_one`: `H_1 = H(Z_1)`.
* `mul_entropy_coordLaw_sub_one_ge` (`lem:sample_entropy`): `(m - 2) H_m + m H(μ) ≤ m H_{m-1}`
  for `2 ≤ m ≤ N`, equivalently `m D_{m-1} ≤ (m - 2) D_m`.
* `klDiv_coordLaw_pi_le_of_completelyLogConcave`: the lemma, from the sequence lemma
  `sequence_lemma` (`lem:sample_entropy`) and `D_1 = 0` (`lem:sample_entropy`).

The strong-hypothesis source interface is now `klDiv_coordLaw_pi_le_of_stronglyLogConcave`;
it uses the proved homogeneous strong/Lorentzian equivalence. The entropy recurrence
consumes the deletion-sum Han theorem before reducing by exchangeability.
-/

public section

open MeasureTheory InformationTheory

namespace Parking

/-- Coordinate `i` of the first `k` coordinates of a word is coordinate `i` of the word:
the law of coordinate `i` under `L(Z_1, …, Z_k)` is the law of `Z_i` under `L`. -/
theorem coordMarginalLaw_coordLaw {N d : ℕ} (L : Measure (Fin N → Fin d)) {k : ℕ}
    (hk : k ≤ N) (i : Fin k) :
    coordMarginalLaw (coordLaw L hk) i = coordMarginalLaw L (Fin.castLE hk i) := by
  rw [coordMarginalLaw, coordLaw,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

/-- `lem:sample_entropy`: if every coordinate of a probability law `L` on
`[d]^N` has law `μ`, then for `m ≤ N`,
`KL(L(Z_1, …, Z_m) ‖ μ^{⊗m}) = m H(μ) - H(Z_1, …, Z_m)`. -/
theorem klDiv_coordLaw_pi_eq_entropy {N d : ℕ} (L : Measure (Fin N → Fin d))
    [IsProbabilityMeasure L] {μ : Measure (Fin d)} [IsProbabilityMeasure μ]
    (hμ : ∀ i, coordMarginalLaw L i = μ) {m : ℕ} (hm : m ≤ N) :
    klDiv (coordLaw L hm) (Measure.pi fun _ : Fin m => μ) =
      ENNReal.ofReal (m * entropy μ - entropy (coordLaw L hm)) := by
  have : IsProbabilityMeasure (coordLaw L hm) := by
    rw [coordLaw]
    infer_instance
  exact klDiv_pi_eq_entropy _ μ fun i => by rw [coordMarginalLaw_coordLaw, hμ]

/-- The entropy of the law of the first coordinate, viewed on `[d]^1`, is the entropy of the
law of `Z_1` on `[d]`. -/
theorem entropy_coordLaw_one {N d : ℕ} (L : Measure (Fin N → Fin d)) (h : 1 ≤ N) :
    entropy (coordLaw L h) = entropy (coordMarginalLaw L ⟨0, h⟩) := by
  have hinj : Function.Injective fun (y : Fin 1 → Fin d) => y 0 := by
    intro y y' hy
    funext i
    rw [Subsingleton.elim i 0]
    exact hy
  rw [← entropy_map_of_injective _ hinj, coordLaw,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

/-- `lem:sample_entropy`: for an exchangeable probability law `L` on
`[d]^N` with Lorentzian count-generating polynomial and coordinates of law `μ`,
and for `2 ≤ m ≤ N`, `(m - 2) H_m + m H(μ) ≤ m H_{m-1}`, where `H_r = H(Z_1, …, Z_r)`.
This is the strengthened Han inequality applied to the law of `(Z_1, …, Z_m)`, which is
exchangeable with completely log-concave count-generating polynomial. -/
theorem mul_entropy_coordLaw_sub_one_ge_of_lorentzian {N d : ℕ} (L : Measure (Fin N → Fin d))
    [IsProbabilityMeasure L] (hL : IsExchangeableLaw L) (h : Lorentzian N (countPoly L))
    {μ : Measure (Fin d)} (hμ : ∀ i, coordMarginalLaw L i = μ) {m : ℕ} (hm2 : 2 ≤ m)
    (hmN : m ≤ N) :
    ((m : ℝ) - 2) * entropy (coordLaw L hmN) + m * entropy μ ≤
      m * entropy (coordLaw L ((Nat.sub_le m 1).trans hmN)) := by
  have : IsProbabilityMeasure (coordLaw L hmN) := by
    rw [coordLaw]
    infer_instance
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  have hex := IsExchangeableLaw.coordLaw L hL hmN
  have hlor := lorentzian_countPoly_coordLaw L hL h hmN
  have key := strongHan_of_lorentzian hm2 (coordLaw L hmN) hex hlor
  have hsumMarg : ∑ j, entropy (coordMarginalLaw (coordLaw L hmN) j) =
      ((r + 1 : ℕ) : ℝ) * entropy μ := by
    simp only [coordMarginalLaw_coordLaw, hμ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hsumDelete : ∑ j, entropy (restrictCoordLaw (coordLaw L hmN) (Finset.univ.erase j)) =
      ((r + 1 : ℕ) : ℝ) * entropy (coordLaw (coordLaw L hmN) (Nat.sub_le (r + 1) 1)) := by
    rw [Finset.sum_congr rfl fun j _ => hex.entropy_restrictCoordLaw_erase j,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      entropy_coordLaw_congr (coordLaw L hmN) (Nat.sub_le (r + 1) 1)
        (Nat.le_succ r) (by omega)]
  rw [hsumMarg, hsumDelete, coordLaw_coordLaw] at key
  exact key

/-- Complete-log-concavity interface for the same source entropy recurrence. -/
theorem mul_entropy_coordLaw_sub_one_ge {N d : ℕ} (L : Measure (Fin N → Fin d))
    [IsProbabilityMeasure L] (hL : IsExchangeableLaw L) (h : CompletelyLogConcave (countPoly L))
    {μ : Measure (Fin d)} (hμ : ∀ i, coordMarginalLaw L i = μ) {m : ℕ} (hm2 : 2 ≤ m)
    (hmN : m ≤ N) :
    ((m : ℝ) - 2) * entropy (coordLaw L hmN) + m * entropy μ ≤
      m * entropy (coordLaw L ((Nat.sub_le m 1).trans hmN)) :=
  mul_entropy_coordLaw_sub_one_ge_of_lorentzian L hL
    (h.stronglyLogConcave.lorentzian (isHomogeneous_countPoly L)) hμ hm2 hmN

/-- `lem:sample_entropy`, Lorentzian
form: let `L` be an exchangeable probability law on `[d]^N`, `N ≥ 2`, whose coordinates all
have law `μ` and whose count-generating polynomial is Lorentzian. Then for
`1 ≤ k ≤ N`, `KL(L(Z_1, …, Z_k) ‖ μ^{⊗k}) ≤ k(k-1)/(N(N-1)) · KL(L ‖ μ^{⊗N})`.

The proof sets `D_m = m H(μ) - H(Z_1, …, Z_m)`, which is `KL(L(Z_1, …, Z_m) ‖ μ^{⊗m})`,
checks `D_1 = 0` and `m D_{m-1} ≤ (m - 2) D_m` for `2 ≤ m ≤ N`, and applies
`sequence_lemma`. -/
theorem klDiv_coordLaw_pi_le_of_lorentzian {N d : ℕ} (hN : 2 ≤ N)
    (L : Measure (Fin N → Fin d)) [IsProbabilityMeasure L] (hL : IsExchangeableLaw L)
    (h : Lorentzian N (countPoly L)) (μ : Measure (Fin d)) [IsProbabilityMeasure μ]
    (hμ : ∀ i, coordMarginalLaw L i = μ) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    InformationTheory.klDiv (coordLaw L hkN) (Measure.pi fun _ : Fin k => μ) ≤
      ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1))) *
        InformationTheory.klDiv L (Measure.pi fun _ : Fin N => μ) := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ,
      ∀ (m : ℕ) (hm : m ≤ N), D m = m * entropy μ - entropy (coordLaw L hm) :=
    ⟨fun m => if hm : m ≤ N then (m : ℝ) * entropy μ - entropy (coordLaw L hm) else 0,
      fun m hm => by simp only [hm, dite_true]⟩
  have hD1 : D 1 = 0 := by
    rw [hD 1 (by omega), entropy_coordLaw_one, hμ, Nat.cast_one, one_mul, sub_self]
  have hrec : ∀ m : ℕ, 2 ≤ m → m ≤ N → (m : ℝ) * D (m - 1) ≤ ((m : ℝ) - 2) * D m := by
    intro m hm2 hmN
    have key := mul_entropy_coordLaw_sub_one_ge_of_lorentzian L hL h hμ hm2 hmN
    rw [hD m hmN, hD (m - 1) ((Nat.sub_le m 1).trans hmN), Nat.cast_sub (by omega : 1 ≤ m),
      Nat.cast_one]
    linarith
  have hseq := sequence_lemma hN D hD1 hrec hk1 hkN
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
  have hDN : D N = N * entropy μ - entropy L := by
    rw [hD N le_rfl, coordLaw_self]
  rw [klDiv_coordLaw_pi_eq_entropy L hμ hkN, klDiv_pi_eq_entropy L μ hμ,
    ← ENNReal.ofReal_mul hc, ← hD k hkN, ← hDN]
  exact ENNReal.ofReal_le_ofReal hseq

/-- Complete-log-concavity interface for the same sample-entropy result. -/
theorem klDiv_coordLaw_pi_le_of_completelyLogConcave {N d : ℕ} (hN : 2 ≤ N)
    (L : Measure (Fin N → Fin d)) [IsProbabilityMeasure L] (hL : IsExchangeableLaw L)
    (h : CompletelyLogConcave (countPoly L)) (μ : Measure (Fin d)) [IsProbabilityMeasure μ]
    (hμ : ∀ i, coordMarginalLaw L i = μ) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    InformationTheory.klDiv (coordLaw L hkN) (Measure.pi fun _ : Fin k => μ) ≤
      ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1))) *
        InformationTheory.klDiv L (Measure.pi fun _ : Fin N => μ) :=
  klDiv_coordLaw_pi_le_of_lorentzian hN L hL
    (h.stronglyLogConcave.lorentzian (isHomogeneous_countPoly L)) μ hμ hk1 hkN

/-- The manuscript's general sample-entropy lemma with its stated strong
log-concavity hypothesis. Homogeneity of the occupation polynomial supplies
exactly the hypothesis of the proved strong/Lorentzian equivalence. -/
theorem klDiv_coordLaw_pi_le_of_stronglyLogConcave {N d : ℕ} (hN : 2 ≤ N)
    (L : Measure (Fin N → Fin d)) [IsProbabilityMeasure L] (hL : IsExchangeableLaw L)
    (h : StronglyLogConcave (countPoly L)) (μ : Measure (Fin d)) [IsProbabilityMeasure μ]
    (hμ : ∀ i, coordMarginalLaw L i = μ) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    InformationTheory.klDiv (coordLaw L hkN) (Measure.pi fun _ : Fin k => μ) ≤
      ENNReal.ofReal ((k : ℝ) * ((k : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1))) *
        InformationTheory.klDiv L (Measure.pi fun _ : Fin N => μ) := by
  exact klDiv_coordLaw_pi_le_of_lorentzian hN L hL
    (h.lorentzian (isHomogeneous_countPoly L)) μ hμ hk1 hkN

end Parking

end
