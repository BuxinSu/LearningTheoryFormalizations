# Appendix formalization: sources, workflow, files, and status

This is the canonical overview of the five consolidated `Appendix_*.lean`
modules.  It records the bibliography, proof pipelines, reusable Lean
infrastructure, file inventory, and current status of UP-004 through UP-008.

The status convention used below is important.  **UP-007 is solved by an
approved two-version replacement**: the source-faithful theorem is proved with
the source's symmetry hypothesis and exact constants, and the theorem without
symmetry is proved with the honest symmetrization losses.  The literal
centered-only exact-constant formula is documented but is not asserted as a
theorem, so the two-version resolution does not silently claim a stronger
result.

## 1. External mathematical and formalization resources

### 1.1 UP-004: Golden--Thompson

The formal proof follows the elementary Lie-product/Dyson route.

Primary presentation:

- J. R. Lee, *CSE 599I: Analysis of Boolean Functions*, Lecture 3,
  [Golden--Thompson and the Frobenius inner product](https://homes.cs.washington.edu/~jrl/teaching/cse599Isp21/notes/lecture3.pdf).
  This supplies the proof organization: Frobenius Cauchy--Schwarz, Dyson's
  finite word argument, disentangling, and the Lie product limit.
- F. J. Dyson (1964), the original finite maximization/disentangling argument
  over words in `A` and `Aᴴ`.
- S. Golden, “Lower bounds for the Helmholtz function,” *Physical Review* 137
  (1965), B1127--B1128.
- C. J. Thompson, “Inequality with applications in statistical mechanics,”
  *Journal of Mathematical Physics* 6 (1965), 1812--1813.

Secondary checks include T. Tao's notes on Golden--Thompson.  The route avoids
the majorization and antisymmetric-tensor machinery used in references such as
Bhatia and Thirring, because that machinery is not available in the pinned
Mathlib.

### 1.2 UP-005: sharp Gaussian concentration

The proof uses Prékopa--Leindler and Gaussian tensorization, followed by a
Laplace-transform/Chernoff argument.

- A. Prékopa (1971, 1973) and L. Leindler (1972): the Prékopa--Leindler
  inequality.
- R. J. Gardner, “The Brunn--Minkowski inequality,” *Bulletin of the AMS* 39
  (2002), §4: the level-set route from one-dimensional Brunn--Minkowski to
  Prékopa--Leindler.
- B. Maurey, “Some deviation inequalities,” *GAFA* 1 (1991), 188--197:
  property `(τ)` and the Gaussian infimum-convolution viewpoint.
- S. G. Bobkov and M. Ledoux, “From Brunn--Minkowski to Brascamp--Lieb and to
  logarithmic Sobolev inequalities,” *GAFA* 10 (2000), §2: Gaussian functional
  inequalities derived from Prékopa--Leindler.
- S. G. Bobkov and F. Götze, “Exponential integrability and transportation
  cost related to logarithmic Sobolev inequalities,” *JFA* 163 (1999): the
  transport/infimum-convolution dual formulation.
- M. Talagrand, “Transportation cost for Gaussian and other product
  measures,” *GAFA* 6 (1996): the Gaussian `T₂` inequality.
- C. Borell (1975) and B. S. Tsirelson, I. A. Ibragimov, V. N. Sudakov
  (1976): classical Gaussian concentration.
- S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities* (2013),
  Theorem 5.6: the book's cited concentration theorem.

Mathlib does not provide the required one-dimensional Brunn--Minkowski or
Prékopa--Leindler theorem, so these are formalized from first principles.
YuanheZ's `lean-stat-learning-theory` is recorded as an alternative
log-Sobolev/Herbst formalization, but it is not a dependency of this project.

### 1.3 UP-006 and UP-007: matrix Rosenthal and Rosenthal--Pinelis

- R. Y. Chen, A. Gittens, J. A. Tropp, “The Masked Sample Covariance
  Estimator,” *Information and Inference* 1 (2012), Appendix A,
  [preprint](https://tropp.caltech.edu/papers/CGT11-Masked-Sample-preprint.pdf)
  (`CGT12a`).
- A. Buchholz, “Operator Khintchine inequality in non-commutative
  probability,” *Mathematische Annalen* 319 (2001), and the 2005 sequel on
  sharp constants.
- M. Junge and Q. Zheng, “Noncommutative Bennett and Rosenthal inequalities,”
  *Annals of Probability* 41 (2013), arXiv:1111.1027.
- L. Mackey, M. I. Jordan, R. Y. Chen, B. Farrell, J. A. Tropp, “Matrix
  concentration inequalities via the method of exchangeable pairs,”
  *Annals of Probability* 42 (2014), Corollary 7.4.
- J. A. Tropp, “The expected norm of a sum of independent random matrices: an
  elementary approach,” *High Dimensional Probability VII* (2016),
  arXiv:1506.04711.

The source-hypothesis audit is decisive for UP-007.  CGT Theorem A.1(2), and
its second-moment specialization Theorem 3.2, concern independent,
**symmetric-in-law self-adjoint summands**.  The proof explicitly inserts
Rademacher signs using that symmetry.  Therefore it gives the exact constants
under symmetry; it is not, by itself, a centered-only theorem.

### 1.4 UP-008: lower bound for symmetric sums

- M. Ledoux and M. Talagrand, *Probability in Banach Spaces* (1991), §6.1;
  Proposition 6.10 is the book's Lévy-type maximal-inequality citation.
- V. H. de la Peña and E. Giné, *Decoupling: From Dependence to Independence*
  (1999), §1.1: symmetrization and reflection arguments.

The Lean proof ultimately avoids a separate Lévy maximal theorem: product-law
sign reflection plus finite sign averaging proves a stronger inequality.

## 2. Formalization workflow and prerequisite toolkit

The appendix is intentionally built upward.  Each difficult theorem is first
reduced to the smallest reusable analytic, algebraic, combinatorial, or
probabilistic tools that Mathlib does not already contain.

```text
trace/Frobenius CS
  -> Dyson word combinatorics
  -> Golden--Thompson                                      (UP-004)

1-D Brunn--Minkowski
  -> 1-D Prékopa--Leindler
  -> Gaussian-adapted PL
  -> finite-product tensorization
  -> Lipschitz MGF and Chernoff
  -> matrix weak-variance Lipschitz reduction + law transfer (UP-005)

finite product-law factorization + sign reflection
  -> deterministic Boolean-sign averaging                  (UP-008)
  -> ghost-copy/Rademacher bounds + psd self-bound          (UP-006)
  -> Schatten audit and two-version Rosenthal--Pinelis      (UP-007)
```

### 2.1 Tools that had to be formalized first

1. **Matrix analytic basics:** vectorization, Frobenius pairing, trace
   Cauchy--Schwarz, positivity/reality of psd traces, matrix exponential
   estimates, and quantitative power telescoping.
2. **Finite noncommutative word combinatorics:** words in `A` and `Aᴴ`, cyclic
   transition counts, rotation, star words, and finite maximization.
3. **Measure/convexity foundations absent from Mathlib:** one-dimensional
   Brunn--Minkowski, measurable-set approximation, layer-cake,
   Prékopa--Leindler, and truncation/monotone convergence.
4. **Product Gaussian infrastructure:** Gaussian density substitution,
   measure-preserving coordinate equivalences, product Fubini, and
   tensorization of the quadratic cost.
5. **Gaussian exponential integrability:** reduce
   `exp(c * ‖x‖)` to coordinatewise `exp(c * |xᵢ|)` using
   `√(Σxᵢ²) ≤ Σ|xᵢ|`, then use the one-dimensional Mathlib Gaussian moment
   theorem and Fubini.
6. **Law-transfer and reflection tools:**
   `ProbabilityTheory.iIndepFun.map_fun_eq_pi_map`, measurable coordinate
   sign flips/pair swaps, invariance of product measures, and transport of
   integrals through map measures.
7. **Rademacher and self-bound tools:** a Boolean Rademacher measure, exact
   finite sign averaging, Chapter 4 matrix Rademacher estimates, psd square
   comparisons, Cauchy--Schwarz for integrals, and scalar quadratic algebra.
8. **UP-007-specific infrastructure:** real-exponent Schatten functionals,
   operator/Schatten/dimension comparisons, Hermitian dilation, explicit
   noncommutative-Khintchine predicates, small-dimension Frobenius estimates,
   and ghost-copy variance/maximal-summand identities.

### 2.2 Practical Lean workflow

- Toolchain: Lean 4 / Mathlib pinned at v4.31.0.
- Probe uncertain API names in a scratch file with `#check` before editing a
  production module.
- Add one dependency layer at a time and keep every Appendix file fully proved.
- Use `lake env lean MatrixConcentration/Appendix_GoldenThompson.lean` for a
  direct elaboration check (substituting any of the other four consolidated
  module names), and `lake build` for the authoritative root build.
- Use `#print axioms` on every claimed discharge; accepted dependencies are
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Finish with a full `lake build`, a forbidden-token scan, and a check that
  each registered book statement has not been silently weakened.

## 3. Proof pipelines and outcomes

### 3.1 UP-004: Golden--Thompson — discharged

1. Vectorize matrices and obtain trace Cauchy--Schwarz from the existing
   vector dot-product inequality.
2. Encode words in `A` and `Aᴴ` by Boolean lists.  Maximize absolute trace and
   cyclic transitions; if a maximizing word is not alternating, rotate and
   split it, then use trace Cauchy--Schwarz to contradict maximality.
3. Deduce Dyson's disentangling chain for powers of products of Hermitian
   matrices.
4. Prove a quantitative Lie product formula using second-order exponential
   estimates and telescoping powers.
5. Apply disentangling at dyadic powers and pass to the limit to obtain
   `tr(exp(A+B)) ≤ tr(exp A * exp B)`.

### 3.2 UP-005: Gaussian concentration — discharged

1. Prove one-dimensional Brunn--Minkowski for compact sets, extend it to
   measurable sets by inner regularity, and derive one-dimensional
   Prékopa--Leindler by level sets, layer-cake, weighted AM--GM, and
   truncation.
2. Substitute the Gaussian density into Prékopa--Leindler.  The completed
   square produces the Gaussian cost
   `p(1-p)(x-y)²/2`.
3. Tensorize this Gaussian-adapted statement over finite products by Fubini
   and measure-preserving coordinate equivalences.
4. For a Lipschitz function `W`, choose three exponential PL test functions.
   Complete the square, use Jensen, and let `p -> 1⁻` to obtain the sharp MGF
   bound `E exp(s(W-EW)) ≤ exp(s²L²/2)`.
5. Apply the sub-Gaussian Chernoff theorem to obtain
   `P(W ≥ EW+t) ≤ exp(-t²/(2L²))`.
6. Show the norm of a rectangular Gaussian matrix series is
   `sqrt(weakVariance)`-Lipschitz, then transfer an arbitrary independent
   standard-Gaussian family to the standard product law.  This discharges the
   registered `gauss_concentration` theorem without changing its statement.

### 3.3 UP-008: symmetric lower bound — discharged

1. Factor the joint law into the product of the marginal laws.
2. Distributional symmetry makes every deterministic Boolean sign flip
   measure preserving.
3. For deterministic vectors, select a largest coordinate and pair every sign
   pattern with the pattern toggled at that coordinate.
4. The two-point norm inequality bounds the largest squared coordinate by the
   signed-sum average.
5. Integrate and use law invariance.  The proof obtains the stronger constant
   `1`, so the registered constant `1/4` follows immediately.

### 3.4 UP-006: matrix Rosenthal — discharged

1. Use an independent ghost copy and Jensen to separate the mean from a
   symmetric difference.
2. Factor the joint law; pair swaps produce all Boolean sign patterns without
   changing the product measure.
3. Bound the ghost term by a conditional one-sided Hermitian Rademacher
   expectation.
4. For psd summands use
   `‖ΣXₖ²‖ ≤ (maxₖ λmax Xₖ) * λmax(ΣXₖ)`.
5. Cauchy--Schwarz gives a scalar quadratic self-bound; completing the square
   yields coefficient `8 log d`, stronger than the registered `8e log d`.

### 3.5 UP-007: solved by the two-version resolution

Set

- `D = d₁ + d₂`,
- `V = max(‖Σ E(SₖSₖᴴ)‖, ‖Σ E(SₖᴴSₖ)‖)`, and
- `M = E maxₖ ‖Sₖ‖²`.

The source and formal theorem statuses are:

| Version | Assumptions | Proven bound | Status |
|---|---|---|---|
| Source-faithful CGT version | independent, measurable, symmetric in law; integrable maximum squared summand | `sqrt(2e V log D) + 4e log D * sqrt(M)` | **proved; exact source constants** |
| Centered ghost-copy version | independent, measurable, centered; integrable maximum squared summand | `sqrt(4e V log D) + 8e log D * sqrt(M)` | **proved; losses `sqrt 2` and `2`** |
| Literal book display | independent and centered under the book's standing regularity convention | `sqrt(2e V log D) + 4e log D * sqrt(M)` | **documented, not asserted as a theorem** |

This verifies the intended interpretation:

- With the additional symmetry-in-law assumption, the formal result has
  exactly the constants of CGT's symmetric second-moment theorem.  Integrable
  symmetry also implies zero expectation, so a separate centering hypothesis
  is unnecessary.
- Without symmetry, introduce an independent copy `S'` and
  `Deltaₖ = Sₖ - S'ₖ`.  Then `Deltaₖ` is independent and symmetric,
  Jensen gives `‖ΣSₖ‖_{L₂} ≤ ‖ΣDeltaₖ‖_{L₂}`, and
  `V_Delta = 2V`, `M_Delta ≤ 4M`.  Substitution produces exactly the losses
  `sqrt 2` and `2` shown above.
- These are losses of this ghost-copy proof.  They do not show that the
  centered exact book display is false, and they do not prove that its optimal
  constants must be larger.

The exact symmetric proof itself has two dimension regimes.  For large `D`,
a Boolean-Rademacher second-moment estimate and the positive matrix Rosenthal
theorem control the random square function.  For small `D`, a centered
Frobenius orthogonality bound gives
`E‖ΣSₖ‖² ≤ min(d₁,d₂)V`; explicit logarithmic/exponential inequalities finish
the constant comparison.  Hermitian dilation transfers the self-adjoint
argument to rectangular matrices without changing either coefficient.

Accordingly, **UP-007 is SOLVED in this project by the source-faithful exact
theorem and the centered theorem with its proven losses**.  This is not a claim
that the third row has been proved.

## 4. File-by-file inventory

| File | Main content | Current role/status |
|---|---|---|
| `Appendix_GoldenThompson.lean` | Frobenius trace Cauchy--Schwarz, Dyson words, Lie product formula, Golden--Thompson | Complete; discharges UP-004 |
| `Appendix_GaussianConcentration.lean` | One-dimensional and Gaussian Prékopa--Leindler, tensorization, Lipschitz matrix concentration | Complete; discharges UP-005 |
| `Appendix_SymmetricLowerBound.lean` | Product-law sign invariance and finite sign averaging | Complete; discharges UP-008 with a stronger constant-one estimate |
| `Appendix_MatrixRosenthal.lean` | Ghost symmetrization, pair reflection, Rademacher and psd self-bound | Complete; discharges UP-006 with a stronger intermediate coefficient |
| `Appendix_RosenthalPinelis.lean` | Schatten comparisons, symmetric exact-coefficient theorem, and centered theorem with losses | Complete; supplies the approved two-version UP-007 resolution |

## 5. Available and missing library infrastructure

Important available Mathlib/project tools include:

- finite product measures, Fubini/Tonelli, `Measure.map`, and
  measure-preserving finite-coordinate equivalences;
- `iIndepFun.map_fun_eq_pi_map` for independent joint-law factorization;
- one-dimensional Gaussian distributions and
  `integrable_exp_mul_gaussianReal`;
- matrix SVD/singular values, spectral norm, Frobenius norm, Hermitian
  dilation, CFC square roots and powers;
- Chapter 4 Hermitian and rectangular Rademacher bounds;
- scalar real powers, finite Hölder/Minkowski, Jensen, and sub-Gaussian
  Chernoff machinery.

The UP-007 feasibility audit found no general variable Schatten norm with its
triangle inequality, Ky Fan dominance, singular-value submajorization, von
Neumann trace inequality, Schatten Hölder/duality, sharp Buchholz
noncommutative Khintchine theorem, or noncommutative `L_p` probability stack in
the pinned Mathlib.  `Appendix_RosenthalPinelis.lean` therefore proves the
available numerical Schatten comparisons and the unconditional integrable
two-version results; conditional reductions are only internal proof
infrastructure.  A future proof of the literal centered exact formula would
require genuinely supplying the missing sharp input, for example a real-exponent coefficient
`kappa_r ≤ sqrt(r/2)` at `r = 2 log D`, or another constant-safe argument.

## 6. Final status and verification

| Registration/project item | Status |
|---|---|
| UP-004 Golden--Thompson | **discharged** |
| UP-005 Gaussian concentration | **discharged** |
| UP-006 matrix Rosenthal | **discharged** |
| UP-007 matrix Rosenthal--Pinelis | **solved by two-version resolution** |
| UP-007 literal centered exact formula | **documented but not asserted** |
| UP-008 symmetric lower bound | **discharged** |

All five consolidated Appendix Lean files contain no `sorry`, `admit`, declared axiom, or
`native_decide`.  The two UP-007 resolution theorems have axiom dependencies
exactly

```text
[propext, Classical.choice, Quot.sound]
```

The literal centered-exact source display is not asserted.  The root module
imports all five consolidated Appendix modules, and the complete project builds
with:

```bash
~/.elan/bin/lake build
```
