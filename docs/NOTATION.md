# Reading the Lean notation

[Overview](../README.md) · [Paper correspondence](RESULTS.md) · [Proof guide](PROOF-GUIDE.md)

The formalization uses the paper's probability laws and parameter ranges. This guide explains their Lean representations; the declarations themselves remain the precise statements.

## Sizes, coordinates and parking words

| Paper | Lean | Interpretation |
| --- | --- | --- |
| Positive size $n$ | `n : ℕ+` | A positive natural number. `(n : ℕ)` and `(n : ℝ)` are its natural and real casts. |
| Coordinate or value in $\{1,\ldots,n\}$ | `i : Fin n` | Zero-based: the paper's value is `i.val + 1`. |
| A word of length $k$ with values in $\{1,\ldots,n\}$ | `Fin k → Fin n` | A function on the finite coordinate set. |
| A parking function | `ParkingFunction n` | A word together with a proof of the parking condition. |
| First $k$ coordinates | `firstCoords n k hkn` | `hkn : k ≤ n` justifies the coordinate inclusion. |

For a word `a : Fin n → Fin n`, [`isParkingFunction`](../Parking/Basic.lean#L45) requires at least `j.val + 1` coordinates with `a i ≤ j`, for each `j : Fin n`. Thus the all-zero Lean word represents the all-ones parking function in the paper. The translation is proved by [`isParkingFunction_iff_one_based`](../Parking/Law.lean#L230); the sorted characterization is [`isParkingFunction_iff_sort_le`](../Parking/Paper/PrefixProduct.lean#L60).

The uniform bounds explicitly assume $n\ge2$ and $1\le k\le n$. The positive-natural encoding does not remove these hypotheses. Limit theorems allow all positive sizes, since changing finitely many sizes does not change a limit at infinity.

## Probability laws and distances

| Paper notation | Lean declaration | Construction |
| --- | --- | --- |
| Uniform parking function $\pi_n$ | [`uniformParking`](../Parking/Law.lean#L79) | Normalized counting law on `ParkingFunction n`. |
| $P_{n,k}$ | [`firstCoordsLaw`](../Parking/Law.lean#L87) | Pushforward of `uniformParking` by the first-coordinate map. |
| $U_n$ | [`uniformLaw (Fin n)`](../Parking/Law.lean#L74) | Uniform probability law on the finite alphabet. |
| $Q_{n,k}=U_n^{\otimes k}$ | [`uniformProduct`](../Parking/Law.lean#L92) | Product of $k$ uniform laws. |
| $\mu_n$ | [`marginal`](../Parking/Law.lean#L100) | First-coordinate marginal of `uniformParking`. |
| $\mu_n^{\otimes k}$ | [`marginalProduct`](../Parking/Law.lean#L111) | Product of $k$ copies of the marginal law. |
| $d_{\mathrm{TV}}(P,Q)$ | [`tvDist`](../Parking/Law.lean#L68) | The real number $\tfrac12\sum_x\lvert P(x)-Q(x)\rvert$. |
| $g_n(j)=n\mu_n(j)-1$ | [`parkingG`](../Parking/Marginal.lean#L61) | The same expression with the index shift described above. |
| $G_n(z)$ | [`countPoly (parkingWordLaw n)`](../Parking/CountPoly.lean#L37) | The occupation generating polynomial. |

`ProbabilityMeasure α` is a measure on `α` with total mass one. An expression such as `(P {x} : ℝ)` is the real mass of the singleton `{x}`. A cast `(P : Measure α)` exposes the underlying measure for Mathlib results such as KL divergence. These are changes of representation, not changes of law. The [singleton formulas](../Parking/Law.lean#L123) make the finite masses explicit.

## Relative entropy and extended values

Mathlib's `InformationTheory.klDiv` takes values in `ℝ≥0∞`, the extended nonnegative reals. `ENNReal.ofReal r` embeds a nonnegative real bound. For the laws used in Proposition 1.3, [`klDiv_firstCoordsLaw_marginalProduct`](../Parking/Law.lean#L303) proves the finite sum formula

$$
D(P\Vert Q)=\sum_x P(x)\log\frac{P(x)}{Q(x)}.
$$

The reference marginal product has full support. The logarithm is the natural logarithm (`Real.log`), and zero-mass terms use the usual zero convention. Proposition 1.3 provides a finite upper bound; the extended-real type allows the general divergence to represent infinity when appropriate.

## Convergence and the profile

`Tendsto f atTop (𝓝 a)` means $f(n)\to a$ as $n\to\infty$. `Tendsto f atTop atTop` means $f(n)\to+\infty$. In the profile theorem, the sequence is indexed by `ℕ+` and the limiting parameter is `lam : ℝ≥0∞`.

The hypothesis embeds the nonnegative ratio $k_n\log n/n$ using `ENNReal.ofReal`. [`tendsto_ofReal_iff`](../Parking/Law.lean#L252) identifies this formulation with ordinary convergence to a finite nonnegative real or divergence to infinity. [`profile`](../Parking/Law.lean#L116) explicitly separates the finite Gaussian formula from the value one at infinity.

The threshold equivalence also has a literal [`Asymptotics.IsLittleO`](../Parking/Corollaries.lean#L125) statement for $k_n=o(n/\log n)$.

## Polynomial properties and constants

[`StronglyLogConcave`](../Parking/LogConcave.lean#L55) uses nonnegative coefficients and concavity of the logarithm of every nonzero iterated coordinate derivative on the positive orthant, including the polynomial itself as the derivative of order zero. [`Lorentzian`](../Parking/Paper/Lorentzian.lean#L43) has an algebraic definition using homogeneous degree, support and quadratic derivatives. Their equivalence for homogeneous polynomials is a [proved theorem](../Parking/Paper/Lorentzian.lean#L209).

Uniform comparison notation such as $a\asymp b$ is expressed by positive constants quantified before all varying parameters. Similarly, a uniform $O(1)$ error is an explicit bound by one constant. For example, [`parkingG_marginal`](../Parking/MarginalSquares.lean#L519) chooses its constants jointly before $n$ and $j$. The original scopes are recorded in the [result correspondence](RESULTS.md).
