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

public import Parking.Paper.RevCSConnected
public import Parking.SupportGenFunCLC

/-!
# Strong log-concavity implies complete log-concavity

This proves the strong/complete part of [BH20, Theorem 2.30] for homogeneous
polynomials using the existing Perron induction. The two properties retain their
independent coordinate-derivative and nonnegative-direction definitions.
-/

public section

open MvPolynomial

namespace Parking

/-- For a quadratic homogeneous polynomial the mixed form is its constant
Hessian, so strong log-concavity implies the reverse Cauchy–Schwarz property. -/
theorem revCS_mixedForm_two_of_stronglyLogConcave {d : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous 2) : RevCS (mixedForm f []) := by
  have heq (u v : Fin d → ℝ) : mixedForm f [] u v = polynomialHessian f 1 u v := by
    have hconst : (dirDeriv u (dirDeriv v f)).IsHomogeneous 0 := by
      simpa using isHomogeneous_dirDeriv (isHomogeneous_dirDeriv hhom v) u
    have hC := totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hconst)
    simp only [mixedForm, List.map_nil, List.prod_nil, Module.End.one_apply,
      polynomialHessian_apply]
    rw [hC]
    simp
  intro u v hu
  rw [heq] at hu
  simpa only [heq] using
    hf.revCS_polynomialHessian hhom le_rfl (x := (1 : Fin d → ℝ)) (fun _ => zero_lt_one) u v hu

/-- All positive mixed directional forms of a homogeneous strongly log-concave
polynomial satisfy reverse Cauchy–Schwarz. Coordinate differentiation preserves
strong log-concavity; its order-zero part supplies connectivity for the Perron
induction. -/
theorem revCS_mixedForm_of_stronglyLogConcave {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m)
    (us : List (Fin d → ℝ)) (hus : us.length + 2 = m)
    (hpos : ∀ u ∈ us, ∀ i, 0 < u i) : RevCS (mixedForm f us) := by
  induction m generalizing f us with
  | zero => omega
  | succ m ih =>
    rcases List.eq_nil_or_concat' us with rfl | ⟨us', w, rfl⟩
    · have hm : m + 1 = 2 := by simpa using hus.symm
      rw [hm] at hhom
      exact revCS_mixedForm_two_of_stronglyLogConcave hf hhom
    · rw [List.length_append, List.length_singleton] at hus
      have hlen : us'.length + 2 = m := by omega
      have hpos' : ∀ u ∈ us', ∀ i, 0 < u i := fun u hu =>
        hpos u (List.mem_append_left _ hu)
      have hw : ∀ i, 0 < w i := hpos w (List.mem_append_right _ (List.mem_singleton_self w))
      refine revCS_mixedForm_append_of_pderiv hhom hf.1 (by omega) hpos' hw
        (hf.reflTransGen_pderiv hhom (by omega)) fun k => ?_
      exact ih (hf.pderiv k) (by simpa using hhom.pderiv (i := k)) us' hlen hpos'

/-- [BH20, Theorem 2.30], strong implies complete for homogeneous polynomials. -/
theorem StronglyLogConcave.completelyLogConcave {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hf : StronglyLogConcave f)
    (hhom : f.IsHomogeneous m) : CompletelyLogConcave f := by
  exact completelyLogConcave_of_revCS f hf.1 hhom
    (revCS_mixedForm_of_stronglyLogConcave hf hhom)

/-- Genuine equivalence of the source's two analytic derivative notions in the
homogeneous setting. -/
theorem stronglyLogConcave_iff_completelyLogConcave {d m : ℕ}
    {f : MvPolynomial (Fin d) ℝ} (hhom : f.IsHomogeneous m) :
    StronglyLogConcave f ↔ CompletelyLogConcave f :=
  ⟨fun h => h.completelyLogConcave hhom, fun h => h.stronglyLogConcave⟩

end Parking

end
