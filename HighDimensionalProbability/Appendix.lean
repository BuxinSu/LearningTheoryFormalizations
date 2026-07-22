import HighDimensionalProbability.Appendix.BoundedDifferences
import HighDimensionalProbability.Appendix.HammingCubeConcentration
import HighDimensionalProbability.Appendix.SymmetricGroupConcentration
import HighDimensionalProbability.Appendix.StronglyConvexDensity
import HighDimensionalProbability.Appendix.PoissonLimitTheorem
import HighDimensionalProbability.Appendix.EuclideanIsoperimetric
import HighDimensionalProbability.Appendix.BerryEsseen
import HighDimensionalProbability.Appendix.TalagrandConvexConcentration
import HighDimensionalProbability.Appendix.SphericalIsoperimetric
import HighDimensionalProbability.Appendix.GaussianIsoperimetric
import HighDimensionalProbability.Appendix.SpecialOrthogonalConcentration
import HighDimensionalProbability.Appendix.GrassmannianConcentration
import HighDimensionalProbability.Appendix.MajorizingMeasureLower
import HighDimensionalProbability.Appendix.BorellConvexBody
import HighDimensionalProbability.Appendix.BrownianReflection

/-!
# HDP isolated appendix results

This is an import-only audit aggregator.  It is deliberately absent from the
package root and every chapter `Main` module. Its active registry contains
fourteen source-faithful proved targets. Brownian reflection, for example, is
proved from finite Gaussian-increment reflection, layer cake, and a vanishing
uniform-grid error.

There are fifteen direct imports because `BorellConvexBody` is retained only
for its proved convex-body domain infrastructure; it is not a registered
target completion. The former assumption-strengthened Gaussian-Chevet and
positive-Ricci targets and the skipped Borell target were removed on
2026-07-20. The entire Lean appendix is proof-placeholder-free and remains
outside the root import graph. Exact source classifications, proof routes,
and axiom results are recorded in `APPENDIX_SUMMARY.md`.
-/
