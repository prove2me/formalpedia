-- Prove2me | solution 1 for UnitDistance.tri_indepRatio_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:14:25.051797+00:00
-- url     : https://prove2.me/submissions/177164a4-c540-4846-93f7-dbb205d82cf1

-- Sol generated from Novelty/UnitDistanceChromaticBridge.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_UnitDistanceGraph
import Theorems.Thm_UnitDistance_tri_indepRatio

/-!
# From planar unit-distance graphs to colouring lower bounds

This file connects the two halves of the project:

* the *geometric* side `Catalog.Novelty.UnitDistanceGraph` (unit-distance graphs of point
  configurations in `ℝ²`), and
* the *combinatorial* side `Catalog.Novelty.IndependenceRatioChromatic` (the independence
  ratio / fractional-chromatic lower bounds).

The main results transfer the abstract inequalities `i(G) < 1/4 ⇒ χ(G) > 4` and
`i(G) < 1/4 ⇒ χ_f(G) > 4` to the concrete class of planar unit-distance graphs.  This is the
exact logical shape of the reduction behind Erdős's 1987 question and the
Matolcsi–Ruzsa–Varga–Zsámboki programme: *a finite planar point set whose unit-distance graph
has independence ratio below `1/4` forces the fractional chromatic number of the plane to
exceed `4`*.

We also record, as a sanity anchor, that the equilateral triangle (independence ratio `1/3`)
does **not** meet the hypothesis: `1/3 > 1/4`.  A genuinely new construction is required to
cross the threshold.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the geometric object and the combinatorial bound compose with no
loss — being a unit-distance graph is irrelevant to the pigeonhole/LP arguments, which only
see the abstract graph.  So the threshold theorems apply verbatim to `unitDistanceGraph p`.
Experiment (Experimenter): specialise `SimpleGraph.four_lt_chromaticNumber_of_indepRatio_lt`
and `SimpleGraph.four_lt_fracValue_of_indepRatio_lt` to `G = unitDistanceGraph p`, and evaluate
the equilateral triangle's ratio via `UnitDistance.tri_indepRatio`.
Analysis (Analyst): the composition is clean precisely because the combinatorial file states
its results for an arbitrary `SimpleGraph` with `[Fintype V]` (no decidability or geometric
hypotheses survive after `omit`).  The triangle computation shows the bound is not vacuously
satisfiable by trivial simplices.
Critique (Critic): the bridge theorems are not tautologies — they assert a strict lower bound
on an `ℕ∞`-valued chromatic number / a `ℚ`-valued fractional value from a purely metric
hypothesis, and the triangle example certifies the hypothesis is a real constraint (it fails
for the triangle).  `hpos` rules out the empty configuration where the ratio is undefined.
Synthesis (PI): together the three files give the full pipeline
`geometry (unit distances) → independence ratio → fractional/integral chromatic lower bound`,
i.e. the engine that converts a sub-`1/4` planar construction into `χ_f(ℝ²) > 4`.
-- !-- end Lab Notes -- !--
-/

open scoped Classical

open UnitDistance

variable {V : Type*} [Fintype V]







open UnitDistance in
theorem solution: (unitDistanceGraph triPoints).indepRatio = 1 / 3 := by
  rw [SimpleGraph.indepRatio]
  simpa using tri_indepRatio
