# From the paper to Lean

[Overview](../README.md) · [Notation](NOTATION.md) · [Proof guide](PROOF-GUIDE.md) · [Verification](VERIFICATION.md)

This guide maps every numbered mathematical result in **A total variation threshold for the first coordinates of uniform parking functions via Lorentzian polynomials**, by Igor Kortchemski, together with its unnumbered introductory consequences. Numbering and source labels refer to the manuscript identified in [provenance](PROVENANCE.md); the arXiv reference will be added when available.

All declaration names below are in the namespace `Parking`, unless a different namespace is written explicitly. File links open the defining declaration. The [notation guide](NOTATION.md) explains how to read its parameters and probability laws.

## The three main results

Let $P_{n,k}$ be the law of the first $k$ coordinates of a uniform parking function, $Q_{n,k}$ the product of $k$ uniform laws, and $\mu_n$ its one-coordinate marginal. The finite-size bounds use $n\ge2$ and $1\le k\le n$.

| Paper | Result | Lean statement | Proof entry point |
| --- | --- | --- | --- |
| Theorem 1.1 (`thm:main`) | Uniform two-sided total variation bounds, with one constant shared by all $n,k$. | [`tvDist_firstCoordsLaw_bounds`](../Parking/Frozen/MainBounds.lean#L38) | [Provider](../Parking/Provider/MainBounds.lean#L38), then [main bound assembly](../Parking/MainTheorem.lean#L131). |
| Theorem 1.2 (`thm:profile`) | Critical Gaussian profile, including zero and infinite parameters. | [`tendsto_tvDist_firstCoordsLaw`](../Parking/Frozen/Profile.lean#L42) | [Provider](../Parking/Provider/Profile.lean#L46), then [profile assembly](../Parking/ProfileTheorem.lean#L124). |
| Proposition 1.3 (`prop:decoupling`) | Joint KL divergence and Pinsker total variation bounds against independent marginals. | [`klDiv_tvDist_firstCoordsLaw_le`](../Parking/Frozen/Decoupling.lean#L41) | [Provider](../Parking/Provider/Decoupling.lean#L46), then [decoupling assembly](../Parking/DecouplingBound.lean#L106). |

For Theorem 1.1, the shared constant $C\ge1$ is chosen before the size and sample-length parameters:

$$
\sqrt{\frac{k\log(k+1)}{Cn+k\log(k+1)}}
\le d_{\mathrm{TV}}(P_{n,k},Q_{n,k})
\le \min\left(1,C\sqrt{\frac{k\log(k+1)}n}\right).
$$

For Theorem 1.2, if $1\le k_n\le n$ and $k_n\log n/n\to\lambda\in[0,\infty]$, then

$$
d_{\mathrm{TV}}(P_{n,k_n},Q_{n,k_n})\longrightarrow F(\lambda),
\qquad
F(\lambda)=
\begin{cases}
2\Phi(\sqrt{\lambda/\pi})-1,&0\le\lambda\lt\infty,\\
1,&\lambda=\infty,
\end{cases}
$$

where $\Phi$ is the standard Gaussian distribution function. The zero-parameter case is included.

For Proposition 1.3, both inequalities are retained in one theorem:

$$
D(P_{n,k}\Vert\mu_n^{\otimes k})
\le \frac{k(k-1)\log n}{n(n-1)},
\qquad
d_{\mathrm{TV}}(P_{n,k},\mu_n^{\otimes k})
\le \sqrt{\frac{k(k-1)\log n}{2n(n-1)}}.
$$

These three declarations are the exact targets listed in [comparator.json](../comparator.json). Their statements also appear in the small [Challenge](../Challenge.lean#L143); their complete proofs are imported by [Solution](../Solution.lean).

## The four lemmas

| Paper | Mathematical content | Lean statement and proof |
| --- | --- | --- |
| Lemma 2.1 (`lem:marginal`) | Monotonicity of $g_n(j)=n\mu_n(j)-1$; uniform density and endpoint bounds; positive lower bound near the left endpoint; $\sum_jg_n(j)^2=(4/\pi)\log n+O(1)$; uniformly bounded cubic sum. | [`parkingG_marginal`](../Parking/MarginalSquares.lean#L519). The constants are chosen jointly before $n$ and $j$. |
| Lemma 2.2 (`lem:occupation_logconcavity`) | Strong log-concavity of the occupation generating polynomial and the product-moment inequality for every positive vector and admissible prefix length. | [`occupation_logconcavity`](../Parking/Paper/OccupationLogConcavity.lean#L39). Both conclusions occur in the same declaration. |
| Lemma 3.1 (`lem:sample_entropy`) | For an exchangeable vector with strongly log-concave occupation polynomial, prefix KL divergence is at most $k(k-1)/[N(N-1)]$ times the full-vector divergence. | [`klDiv_coordLaw_pi_le_of_stronglyLogConcave`](../Parking/SampleEntropy.lean#L192). This retains the stated strong log-concavity hypothesis. |
| Lemma 4.1 (`lem:products`) | $d_{\mathrm{TV}}(\mu_n^{\otimes k},Q_{n,k})\asymp\min(1,\sqrt{k\log(k+1)/n})$, uniformly in $n\ge2$ and $1\le k\le n$. | [`tvDist_marginalProduct_comparable`](../Parking/ProductsProved.lean#L42), using the [product comparison argument](../Parking/Products.lean#L53). |

## Introductory consequences

These statements occur in the abstract or introductory prose; they are not assigned new corollary numbers here.

| Paper assertion | Lean statement and proof |
| --- | --- |
| Uniform comparison $d_{\mathrm{TV}}(P_{n,k},Q_{n,k})\asymp\min(1,\sqrt{k\log(k+1)/n})$. | [`tvDist_firstCoordsLaw_comparable`](../Parking/Corollaries.lean#L45). |
| Total variation tends to zero exactly when $k_n\log n/n\to0$. | [`tendsto_tvDist_firstCoordsLaw_zero_iff`](../Parking/Corollaries.lean#L83). |
| The same threshold in literal little-o notation: $k_n=o(n/\log n)$. | [`tendsto_tvDist_firstCoordsLaw_zero_iff_isLittleO`](../Parking/Corollaries.lean#L125). |
| Above the threshold, $k_n\log n/n\to\infty$ implies total variation tends to one. | [`tendsto_tvDist_firstCoordsLaw_one_of_kLogDiv_atTop`](../Parking/Corollaries.lean#L140). |

The sequence statements quantify over every $k:\mathbb N_{>0}\to\mathbb N$ satisfying $1\le k_n\le n$.

## Remark 2.3: the separate geometric argument

The Pitman–Stanley remark has its own geometric development. It concerns actual Euclidean volume, including nonnegative parameters with zero coordinates.

| Geometric step | Lean statement and proof |
| --- | --- |
| The Pitman–Stanley polytope equals its stated Minkowski sum of suffix simplices. | [`pitmanStanleyPolytope_eq_minkowskiSum`](../Parking/Paper/PitmanStanleyMinkowski.lean#L211). |
| The parking-word polynomial equals $n!$ times the polytope volume. | [`factorial_mul_volume_pitmanStanley`](../Parking/Paper/PitmanStanleyFormula.lean#L79). |
| The occupation polynomial is $n!/(n+1)^{n-1}$ times the volume polynomial. | [`eval_countPoly_eq_volume_pitmanStanley`](../Parking/Paper/PitmanStanleyFormula.lean#L90). |
| The concrete Minkowski-volume polynomial is Lorentzian. | [`pitmanStanley_volume_polynomial_lorentzian`](../Parking/Paper/PitmanStanleyFormula.lean#L113). |
| The combined conclusion of Remark 2.3: a positive volume factor and Lorentzianity of the occupation polynomial. | [`pitmanStanley_occupation_remark`](../Parking/Paper/PitmanStanleyFormula.lean#L126). |

This proves the cited geometric specialization used in the paper. It does not assert a formalization of the general convex-body theorem or all of Alexandrov–Fenchel theory. The [proof guide](PROOF-GUIDE.md#the-geometric-remark) explains its separate route.

## Verification scope

All linked implementation declarations belong to the project build and implementation kernel audit. The Comparator record selects only Theorems 1.1 and 1.2 and Proposition 1.3; the other results are not separate Comparator targets. See [verification evidence](VERIFICATION.md) for the exact revisions and checks, and [Challenge fidelity](CHALLENGE-FIDELITY.md) for the selected interfaces.

Historical narrative, the paper's figure and its AI-use account are not additional mathematical targets. [Errata and deviations](ERRATA-AND-DEVIATIONS.md) records the encodings and elaborations; [provenance](PROVENANCE.md) identifies the source and the limits of the review claims.
