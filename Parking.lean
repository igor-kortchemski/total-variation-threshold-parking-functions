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

public import Parking.Basic
public import Parking.Borel
public import Parking.BorelAsymptotics
public import Parking.BorelEndpoint
public import Parking.BorelTail
public import Parking.Breakpoint
public import Parking.CharFunExpansion
public import Parking.CLCCriterion
public import Parking.Count
public import Parking.CountPoly
public import Parking.Corollaries
public import Parking.DecouplingBound
public import Parking.Entropy
public import Parking.EntropyKL
public import Parking.Exchangeable
public import Parking.External
public import Parking.FirstCoordCount
public import Parking.GaussianValue
public import Parking.KLContraction
public import Parking.Law
public import Parking.Khintchine
public import Parking.LikelihoodLaw
public import Parking.LlrLimit
public import Parking.LogConcave
public import Parking.MConvexForms
public import Parking.MainTheorem
public import Parking.MainScalar
public import Parking.MainScalarPaper
public import Parking.Marginal
public import Parking.MarginalBounds
public import Parking.MarginalSquares
public import Parking.MarginalSquareSource
public import Parking.MixedForm
public import Parking.Occupation
public import Parking.OccupationCounting
public import Parking.Paper.OccupationLogConcavity
public import Parking.Paper.PitmanStanleyFormula
public import Parking.PerronStep
public import Parking.Pinsker
public import Parking.PrefixLaw
public import Parking.ProductMoments
public import Parking.ProductScore
public import Parking.ProfileTheorem
public import Parking.Products
public import Parking.ProductsProved
public import Parking.ProxyMarginal
public import Parking.ProxySums
public import Parking.ProxyTV
public import Parking.RevCauchySchwarz
public import Parking.SampleEntropy
public import Parking.ScoreTV
public import Parking.Separation
public import Parking.SequenceLemma
public import Parking.SqrtSums
public import Parking.StrongHan
public import Parking.SupportGenFunCLC
public import Parking.Symmetrization
public import Parking.TVDist
public import Parking.WordLaw

/-!
# Parking functions

Formalization of the source paper. The laws, distances and profile used in the main
statements are in `Parking.Law`. Proved without hypothesis: the counting results
(`Parking.Count`, `Parking.Breakpoint`, `Parking.FirstCoordCount`), `lem:marginal`
(`Parking.MarginalSquares`), the entropy and log-concavity tools leading to
`lem:sample_entropy` with its strong log-concavity hypothesis (`Parking.SampleEntropy`), and the
analytic steps of `lem:products`, `thm:main` and `thm:profile`.

The library includes the Borel endpoint-tail marginal estimates, genuine
strong/complete/Lorentzian equivalences, prefix-product support normalization,
the displayed KL and scalar chains, the introductory corollaries, and the
separate geometric Pitman–Stanley volume-polynomial remark.

The main results are first proved conditionally, on the hypotheses of `Parking.External`:
`prop:decoupling` on `BH20.SupportGenFunCLC` (`Parking.DecouplingBound`), `thm:main` on `BH20.SupportGenFunCLC` and `AKVZ26.ProductTV`
(`Parking.MainTheorem`) and `thm:profile` on `BH20.SupportGenFunCLC` (`Parking.ProfileTheorem`). Both hypotheses
are then proved: `BH20.SupportGenFunCLC` in `Parking.SupportGenFunCLC` (`bh20_supportGenFunCLC`) and `AKVZ26.ProductTV` in
`Parking.ProxyTV` (`akvz26_productTV`). The statements in `Parking/Frozen/` are proved by the modules in
`Parking/Provider/` and are built separately from this library aggregator.
-/
