# Lean Learning Theory Formalizations

This repository contains two substantial Lean 4 and Mathlib formalizations in learning theory, high-dimensional geometry, and random matrix theory:

- Roman Vershynin’s [*High-Dimensional Probability*](https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-2.pdf), second edition;
- Joel A. Tropp’s [*An Introduction to Matrix Concentration Inequalities*](https://arxiv.org/abs/1501.01571v1).

Together, the libraries develop a reusable formal foundation for concentration inequalities, random vectors, random matrices, matrix analysis, random processes, chaining, dimension reduction, covariance estimation, and sparse recovery.

## Projects

| Project | Mathematical source | Scope | Detailed documentation |
|---|---|---|---|
| HighDimensionalProbability | Roman Vershynin, *High-Dimensional Probability*, second edition | Nine chapters covering concentration, high-dimensional random vectors and matrices, dependent concentration, quadratic forms, random processes, chaining, and matrix deviation | [`HighDimensionalProbability/README.md`](HighDimensionalProbability/README.md) |
| MatrixConcentration | Joel A. Tropp, *An Introduction to Matrix Concentration Inequalities*, arXiv:1501.01571v1 | Matrix analysis, the matrix Laplace-transform method, Gaussian and Rademacher series, Chernoff and Bernstein inequalities, intrinsic dimension, applications, and Lieb’s theorem | [`MatrixConcentration/README.md`](MatrixConcentration/README.md) |

Both project READMEs include chapter-by-chapter Book → Lean correspondence tables that identify the Lean declaration and final module associated with each published source result.

## Repository layout

```text
.
├── HighDimensionalProbability/
│   ├── Prelude/
│   ├── Chapter1_AnalysisAndProbabilityRefresher.lean
│   ├── …
│   ├── Chapter9_DeviationsOfRandomMatricesOnSets.lean
│   └── README.md
├── MatrixConcentration/
│   ├── Prelude.lean
│   ├── Chapter1_Introduction.lean
│   ├── …
│   ├── Chapter8_ProofOfLiebsTheorem.lean
│   ├── Appendix_*.lean
│   └── README.md
├── HighDimensionalProbability.lean
├── MatrixConcentration.lean
├── lakefile.toml
└── lean-toolchain
```

The separately maintained, unresolved appendix subtree of `HighDimensionalProbability` is intentionally excluded from this publication. The `MatrixConcentration` appendix modules are included because they provide completed formal proofs of external ingredients cited by Tropp.

## Build

The repository is pinned to Lean and Mathlib `v4.31.0`.

Build both libraries from the repository root:

```sh
lake build
```

Build one library:

```sh
lake build HighDimensionalProbability
lake build MatrixConcentration
```

Check an individual module:

```sh
lake env lean HighDimensionalProbability/Chapter4_RandomMatrices.lean
lake env lean MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean
```

## HighDimensionalProbability

The Vershynin development formalizes the main arc of high-dimensional probability:

- classical probability and analytic foundations;
- subgaussian and subexponential concentration;
- random vectors, covariance, and high-dimensional geometry;
- random matrices and singular-value estimates;
- concentration without independence;
- quadratic forms, symmetrization, contraction, and decoupling;
- Gaussian and Rademacher processes;
- covering numbers, Dudley bounds, and generic chaining;
- matrix deviation and applications to embeddings, recovery, and restricted isometries.

Its published correspondence table records 566 verified source results. See the [project README](HighDimensionalProbability/README.md) for the complete chapter-by-chapter map.

## MatrixConcentration

The Tropp development formalizes:

- Hermitian and rectangular matrix analysis;
- matrix-valued probability and variance statistics;
- the matrix Laplace-transform method;
- Gaussian and Rademacher matrix series;
- matrix Chernoff and Bernstein inequalities;
- intrinsic-dimension refinements;
- covariance estimation and randomized matrix approximation;
- Lieb’s concavity theorem and cited proof ingredients.

Its published correspondence table records 469 kernel-checked declarations associated with the monograph. See the [project README](MatrixConcentration/README.md) for the complete chapter-by-chapter map and appendix bibliography.

## Namespace conventions

- Vershynin-related declarations use the `HDP` namespace, including `HDP.Chapter1` through `HDP.Chapter9`.
- Tropp-related declarations use the `MatrixConcentration` namespace.

The HighDimensionalProbability library reuses the completed Gaussian-concentration infrastructure from MatrixConcentration, so both libraries are built together in this repository.

## Sources

```bibtex
@misc{vershynin2026high,
  title={High-Dimensional Probability},
  author={Vershynin, Roman},
  year={2026},
  url={https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-2.pdf}
}

@article{tropp2015introduction,
  title={An Introduction to Matrix Concentration Inequalities},
  author={Tropp, Joel A.},
  journal={arXiv preprint arXiv:1501.01571},
  year={2015}
}
```
