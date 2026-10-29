# Exploring the proofs

[Overview](../README.md) · [Paper correspondence](RESULTS.md) · [Notation](NOTATION.md) · [Verification](VERIFICATION.md)

Start with the [result table](RESULTS.md) to locate a theorem. For the three main results, the short files in `Parking/Frozen/` show their public statements and delegate to `Parking/Provider/`. Each provider supplies the proved ingredients to the longer argument. The directions below follow the mathematics rather than alphabetical module order.

## The probability model

[Basic](../Parking/Basic.lean) defines parking functions and occupation counts. [Law](../Parking/Law.lean) constructs the uniform law, its coordinate projections, the product reference laws, total variation and the limiting profile. [Count](../Parking/Count.lean#L264) proves the parking-function cardinality. [WordLaw](../Parking/WordLaw.lean) expresses the parking measure on the full space of words, which is convenient for exchangeability and entropy arguments.

## Marginal estimates: Lemma 2.1

The entry point is [`parkingG_marginal`](../Parking/MarginalSquares.lean#L519). Its proof combines the following steps:

1. [First-coordinate counting](../Parking/FirstCoordCount.lean) gives the exact marginal identities in [Marginal](../Parking/Marginal.lean), including monotonicity, reflection and endpoint values.
2. [BorelAsymptotics](../Parking/BorelAsymptotics.lean), [BorelEndpoint](../Parking/BorelEndpoint.lean) and [BorelTail](../Parking/BorelTail.lean) turn those identities into endpoint-tail estimates.
3. [MarginalBounds](../Parking/MarginalBounds.lean) obtains the pointwise bounds and bounded cubic sum. [MarginalSquareSource](../Parking/MarginalSquareSource.lean) and [MarginalSquares](../Parking/MarginalSquares.lean) assemble the logarithmic second moment.

## Occupation structure: Lemma 2.2

The entry point is [`occupation_logconcavity`](../Parking/Paper/OccupationLogConcavity.lean#L39), which packages the polynomial property and the product-moment bound.

1. [PrefixProduct](../Parking/Paper/PrefixProduct.lean#L127) proves strong log-concavity of the product of prefix linear forms. Its [support identity](../Parking/Paper/PrefixProduct.lean#L118) connects that product to parking occupation vectors.
2. [SupportNormalization](../Parking/Paper/SupportNormalization.lean), [SupportGenFunCLC](../Parking/SupportGenFunCLC.lean) and [OccupationCounting](../Parking/OccupationCounting.lean) justify factorial normalization and the exact occupation probabilities. [Occupation](../Parking/Occupation.lean#L71) concludes strong log-concavity of the occupation polynomial.
3. [PrefixLaw](../Parking/PrefixLaw.lean) transfers the structure to initial coordinate segments. [ProductMoments](../Parking/ProductMoments.lean#L272) proves the expectation bound used later in the separation argument.

The general analytic and algebraic definitions are in [LogConcave](../Parking/LogConcave.lean) and [Lorentzian](../Parking/Paper/Lorentzian.lean). The [notation guide](NOTATION.md#polynomial-properties-and-constants) explains their relationship.

## Entropy approximation: Lemma 3.1 and Proposition 1.3

[StrongHan](../Parking/StrongHan.lean) supplies the strengthened entropy inequality. [SampleEntropy](../Parking/SampleEntropy.lean#L192) applies it to exchangeable prefixes and derives the quadratic factor $k(k-1)/[N(N-1)]$, with [SequenceLemma](../Parking/SequenceLemma.lean) handling the recurrence.

[EntropyKL](../Parking/EntropyKL.lean#L345) identifies the full parking-vector divergence and [bounds it by $\log n$](../Parking/EntropyKL.lean#L381). [DecouplingBound](../Parking/DecouplingBound.lean#L106) combines that estimate with the sample-entropy lemma and [Pinsker](../Parking/Pinsker.lean). The final [provider](../Parking/Provider/Decoupling.lean#L46) supplies the proved log-concavity input and exports the joint KL/TV statement.

## Uniform bounds: Lemma 4.1 and Theorem 1.1

[Products](../Parking/Products.lean#L53) compares the independent marginal product with the uniform product. [ProxyMarginal](../Parking/ProxyMarginal.lean) and [ProxySums](../Parking/ProxySums.lean) estimate the scalar quantities used in that comparison. [ProxyTV](../Parking/ProxyTV.lean#L475) proves the required product-TV interface; [ProductsProved](../Parking/ProductsProved.lean#L42) applies it to obtain Lemma 4.1.

[MainTheorem](../Parking/MainTheorem.lean#L131) combines product comparison and decoupling for the upper bound and the small-scale lower bound. [MainScalarPaper](../Parking/MainScalarPaper.lean) supplies the intermediate scalar estimates. [Separation](../Parking/Separation.lean#L139) uses the occupation product-moment inequality to control the large-scale regime. The final assembly chooses one constant valid for both sides and all admissible parameters; [MainBounds](../Parking/Provider/MainBounds.lean#L38) supplies the remaining proved input.

[Corollaries](../Parking/Corollaries.lean) derives the abstract's uniform comparison, the exact vanishing threshold and convergence to one above the threshold.

## Critical profile: Theorem 1.2

[LikelihoodLaw](../Parking/LikelihoodLaw.lean#L50) represents product total variation using the log-likelihood ratio. [CharFunExpansion](../Parking/CharFunExpansion.lean) controls its characteristic-function remainder, and [LlrLimit](../Parking/LlrLimit.lean#L245) proves the Gaussian limit using the marginal second and third moments.

[GaussianValue](../Parking/GaussianValue.lean#L150) evaluates the limiting expectation, including zero variance. [ProfileTheorem](../Parking/ProfileTheorem.lean#L124) combines this with decoupling for finite parameters and with separation for the infinite parameter. The final [profile provider](../Parking/Provider/Profile.lean#L46) discharges the log-concavity input.

## The geometric remark

Remark 2.3 follows a separate route through [PitmanStanley](../Parking/Paper/PitmanStanley.lean), [PitmanStanleyMinkowski](../Parking/Paper/PitmanStanleyMinkowski.lean), [PitmanStanleyVolume](../Parking/Paper/PitmanStanleyVolume.lean), and the parking-box modules. [PitmanStanleyFormula](../Parking/Paper/PitmanStanleyFormula.lean#L126) combines the actual volume formula and the Lorentzian property of the specific volume polynomial. This provides the paper's alternative geometric explanation; the main occupation proof above uses prefix-product support normalization.

## Conditional interfaces and completed proofs

Some intermediate theorems have names ending in `_of_BH20` or `_of_AKVZ26` and accept a named mathematical input. Those dependencies are explicit in [External](../Parking/External.lean). They are discharged by [`bh20_supportGenFunCLC`](../Parking/SupportGenFunCLC.lean#L178) and [`akvz26_productTV`](../Parking/ProxyTV.lean#L475), which are proved in this library. The main exported statements do not assume those interfaces.

The library uses Mathlib for general foundations, measure theory and analysis, including characteristic-function convergence. The local proofs of cited interfaces concern the versions needed by this manuscript; they do not claim to formalize every generalization in the cited articles. [Provenance](PROVENANCE.md) and [errata and deviations](ERRATA-AND-DEVIATIONS.md) give the scope details.

## Why does Challenge contain `sorry`?

[Challenge](../Challenge.lean) is the small statement interface for the three selected results. It includes their concrete definitions and exactly three deliberate proof placeholders. [Solution](../Solution.lean) imports the complete proofs with the same names and types. Comparator checks the correspondence and verifies the Solution proofs under its permitted-axiom policy.

The implementation has no proof holes and does not import Challenge. For browsing complete proofs, follow the statement/proof links in [Results](RESULTS.md). For reuse, `Parking` exposes the implementation library; the three preserved main exports are available through `Solution`. See [Challenge fidelity](CHALLENGE-FIDELITY.md) for the detailed interface checks and [verification](VERIFICATION.md) for exact checked revisions.
