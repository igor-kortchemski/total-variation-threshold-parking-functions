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

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Shannon entropy of a law on a finite set

Natural logarithm and convention `0 log 0 = 0` (`lem:sample_entropy`;
[LS26, §3.1]).
-/

@[expose] public section

open MeasureTheory

namespace Parking

/-- Shannon entropy, with natural logarithm, of a law on a finite set
(`lem:sample_entropy`; [LS26, §3.1]). -/
noncomputable def entropy {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) : ℝ :=
  ∑ x, Real.negMulLog (μ.real {x})

end Parking

end
