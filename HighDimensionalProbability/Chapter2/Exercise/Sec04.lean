import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums

/-!
# Book Chapter 2 exercises for Section 2.4

Exercise 2.17 is a counterexample/construction task, not a proof-question exercise.
It is intentionally skipped under the exercise policy; no later declaration uses a
chosen estimator or witness.

Exercise 2.16 supplies the rigorous integer-block repair used by the
median-of-means main theorem. Its authoritative declaration is
`medianOfMeans_theorem_2_4_1` in the Section 2.4 core module, so this leaf does
not redeclare it.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

end HDP.Chapter2
