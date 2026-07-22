# Forward-dependency `sorry` ledger

Static source census date: 2026-07-20.

There are **zero open category-C or category-D deferrals** and no
`FORWARD-SORRY-NNN` declarations in Chapters 1--9. No `Deferred.lean` file
exists or is needed. Source-level import inspection finds no later-to-earlier
chapter edge, no numbered-core import of an `Exercise/` leaf or the isolated
Appendix, and no package-root import of the Appendix.

The current executable-placeholder census is **228 category A + 0 category B
= 228 literal `sorry` proof occurrences**. The Appendix registry has a
different, semantic denominator: **14 registered targets = 14 source-faithful
proved + 0 assumption-strengthened proved + 0 skipped**. The former
arbitrary-set Chevet, positive-Ricci, and Borell conditional interfaces were
removed on 2026-07-20; Brownian reflection remains source-faithful proved.

Current compiled axiom evidence records no `sorryAx` or nonstandard axiom on
the Appendix surface.  Authoritative post-correction root and Appendix build
results are recorded in the Lean project's `REVIEW_NOTES.md`.

## Executable placeholder census

The executable-proof census uses a line-level `sorry` search reconciled with
the adjacent category tag and containing declaration. Raw occurrences of
`EXERCISE-SORRY`, `APPENDIX-UNRESOLVED`, or `sorry` in prose and docstrings
are not proof counts.

| Scope | Literal A | Literal B | C | D |
|---|---:|---:|---:|---:|
| Chapter 1 Exercise leaves | 5 | 0 | 0 | 0 |
| Chapter 2 Exercise leaves | 44 | 0 | 0 | 0 |
| Chapter 3 Exercise leaves | 27 | 0 | 0 | 0 |
| Chapter 4 Exercise leaves | 34 | 0 | 0 | 0 |
| Chapter 5 Exercise leaves | 7 | 0 | 0 | 0 |
| Chapter 6 Exercise leaves | 32 | 0 | 0 | 0 |
| Chapter 7 Exercise leaves | 14 | 0 | 0 | 0 |
| Chapter 8 Exercise leaves | 34 | 0 | 0 | 0 |
| Chapter 9 Exercise leaves | 31 | 0 | 0 | 0 |
| Isolated Appendix modules | 0 | 0 | 0 | 0 |
| **Whole source tree** | **228** | **0** | **0** | **0** |

Thus the current source contains exactly **228 executable `sorry` proofs**,
all of them non-load-bearing category-A exercise leaves.

## Former category-B declarations

The following rows are historical provenance. None of the named conditional
interfaces remains in the active Lean source.

| Historical ID | Book source | Current Lean surface | File | Current status |
|---|---|---|---|---|
| `APPENDIX-UNRESOLVED-001` | Book Exercise 8.39(a), prompt physical 268 / printed 260; hint physical 320 / printed 312; related Remark 8.6.3 physical 260 / printed 252 | former arbitrary-set Chevet class and consumers | deleted `Appendix/GaussianChevet.lean` plus former core consumers | RESOLVED BY REMOVAL on 2026-07-20; finite-set Chevet remains in core with explicit `0 ∈ T`, and Exercise 8.39(b) remains covered. |
| `APPENDIX-UNRESOLVED-002` | Book equation (5.8), physical 156 / printed 148 | former positive-Ricci conditional family | deleted `Appendix/PositiveRicciConcentration.lean` | RESOLVED BY REMOVAL on 2026-07-20; reusable Bakry--Émery infrastructure remains. |
| `APPENDIX-UNRESOLVED-003` | Book Example 3.4.6, physical 83--84 / printed 75--76 | former Borell principle and conditional specialization | retained `Appendix/BorellConvexBody.lean` support module | RESOLVED BY REMOVAL on 2026-07-20; five unconditional domain-support declarations remain. |
| `APPENDIX-UNRESOLVED-004` | Book Remark 7.2.1, physical 207 / printed 199 | `HDP.Chapter7.brownianReflectionPrinciple_external` | `Appendix/BrownianReflection.lean` | Source-faithful PROVED by finite-grid reflection and a vanishing mesh error; no literal placeholder. |

## Semantic Appendix registry

The registry count is not a count of literal placeholders:

| Registry status | Count | Meaning |
|---|---:|---|
| Source-faithful PROVED | 14 | Exact registered book targets with complete proofs. |
| Assumption-strengthened PROVED | 0 | The former Q1/Q2 source-facing interfaces were removed. |
| SKIPPED | 0 | The former Q3 source-facing interface was removed. |
| **Total registry** | **14** | **14 source-faithful + 0 strengthened + 0 skipped.** |

## Reconciliation with the superseded census

The 2026-07-15 frozen ledger reported `231 A + 15 B = 246`. That snapshot is
historical, not current:

- Book Exercises 3.43, 3.45, and 3.46
  (`HDP.Chapter3.exercise_3_43`, `HDP.Chapter3.exercise_3_45`, and
  `HDP.Chapter3.exercise_3_46`) were removed from
  `Chapter3/Exercise/Sec04.lean` after their mathematical content was
  promoted and proved in consolidated Chapter 3. They are no longer
  category-A rows. Exercise 3.44 remains deferred.
- Every former Appendix category-B placeholder is gone. Brownian reflection
  is source-faithful proved. The arbitrary-set Chevet, positive-Ricci, and
  Borell source-facing conditional interfaces were removed on 2026-07-20.

## Isolation and final gates

The current source organization keeps exercise leaves and Appendix modules
outside numbered core. Static import inspection confirms that the package
root and consolidated numbered core reach neither an Exercise leaf nor the
Appendix.  The current Appendix axiom census is clean within
`{propext, Classical.choice, Quot.sound}` and records zero `sorryAx` rows.
Exact post-correction build results are centralized in
`HighDimensionalProbability/REVIEW_NOTES.md`.

The earlier 159-target and `31 A / 15 B` negative-harness results may be
retained only as dated history; they are not current final-gate evidence.

## Open category-D entries

| Identifier | Stating chapter | Declaration | Later prerequisite | Status |
|---|---:|---|---|---|
| _None_ | -- | -- | -- | -- |

No category-D declaration or undischarged forward prerequisite exists in
Chapters 1--9.
