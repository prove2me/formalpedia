-- Prove2me | solution 1 for GeomFrac.geomFrac_gt_four_of_indep_ratio
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:25:31.073281+00:00
-- url     : https://prove2.me/submissions/cbe64480-595a-4212-8c0b-391d51a68513

-- Sol generated from Geometry/GeomFractionalChromatic.lean
import Mathlib
import Definitions.Def_Geometry_GeomFractionalChromatic
import Theorems.Thm_GeomFrac_geomFrac_ge_ratio
import Theorems.Thm_GeomFrac_indepNum_pos
/-
Copyright (c) 2026. All rights reserved.

# Geometric Fractional Chromatic Number: the independence-ratio engine

This file develops, from first principles, the linear-programming lower bound that
drives the Matolcsi–Ruzsa–Varga–Zsámboki (`MRVZ`) programme on the fractional
chromatic number of the plane, following the strategy of de Grey (`deGrey`) and the
classical Erdős framing (`Er87`).

The *geometric fractional chromatic number* of a finite graph `G` is the value of the
covering linear program: assign nonnegative weights to the independent sets so that
every vertex is covered with total weight at least `1`, and minimise the total weight.
We model a feasible point as a `FracColoring` and define `geomFrac G` as the infimum of
the achievable totals.

## Main results

* `FracColoring.card_le_indepNum_mul_total` — the LP-duality core:
  `|V| ≤ α(G) · total(c)` for every feasible fractional coloring `c`,
  where `α(G) = G.indepNum` is the independence number.  This is a genuine
  double-counting / weak-duality argument.
* `geomFrac_ge_ratio` — consequently `|V| / α(G) ≤ geomFrac G`.
* `geomFrac_gt_four_of_indep_ratio` — **the key technical mechanism**: if the
  independence ratio is below `1/4` (i.e. `4 · α(G) < |V|`), then
  `geomFrac G > 4`.  This is exactly the reduction used by `MRVZ`: a finite
  unit-distance graph with independence ratio `< 1/4` has fractional chromatic
  number strictly above `4`, hence so does the plane.
* `geomFrac_le_card` — the trivial singleton coloring gives `geomFrac G ≤ |V|`.

The geometric (unit-distance) instantiation lives in `UnitDistanceFractional.lean`.
-/

open SimpleGraph Finset
open scoped BigOperators

open GeomFrac

variable {V : Type*} [Fintype V] [DecidableEq V]


open FracColoring

variable {G : SimpleGraph V}


















/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  The Matolcsi–Ruzsa–Varga–Zsámboki bound
"`χ_f(plane) > 4`" is not really a plane statement: it is a *finite* statement about
one unit-distance graph with independence ratio below `1/4`.  Conjecture: the entire
plane-to-graph reduction is captured by the single inequality
`geomFrac G ≥ |V| / α(G)`, so that `4·α(G) < |V|` alone forces `geomFrac G > 4`.

**Experiment (Experimenter).**  We modelled the covering LP by `FracColoring` and
proved the weak-duality inequality `|V| ≤ α(G)·total(c)` by double counting
vertex–set incidences (`double_count`, `card_le_indepNum_mul_total`).  Taking the
infimum over feasible points gave `geomFrac_ge_ratio`, and the strict corollary
`geomFrac_gt_four_of_indep_ratio` followed by real arithmetic.

**Analysis (Analyst).**  The proof needs only: (i) independent sets have size `≤ α`;
(ii) the covering constraints; (iii) nonnegativity.  No geometry enters the engine —
geometry only supplies a graph `G` with `4·α(G) < |V|`.  The singleton coloring shows
feasibility and gives `geomFrac ≤ |V|`, so the LP value is finite and the infimum is
well posed.

**Critique (Critic).**  Is the statement vacuous?  No: `geomFrac_le_card` shows the
feasible set is nonempty and the value is a real infimum, and
`geomFrac_gt_four_of_indep_ratio` is discharged by genuine arithmetic (`linarith`,
`div_le_iff₀`), not `decide`.  The hypothesis `4·α(G) < |V|` is exactly the MRVZ
independence-ratio condition and is not always satisfiable (it fails for bipartite
graphs, where `α ≥ |V|/2`), so the theorem is not trivially true.

**Synthesis (PI).**  The engine is domain-free and reusable.  The geometric payload —
building `G` with small independence ratio from unit distances — is isolated in
`UnitDistanceFractional.lean`.
-/
open GeomFrac in
theorem solution(G : SimpleGraph V)
    (h : 4 * G.indepNum < Fintype.card V) : 4 < geomFrac G := by
  have hcard : 0 < Fintype.card V := lt_of_le_of_lt (Nat.zero_le _) h
  have : Nonempty V := Fintype.card_pos_iff.mp hcard
  have hα : 0 < G.indepNum := indepNum_pos G
  have hαR : (0 : ℝ) < (G.indepNum : ℝ) := by exact_mod_cast hα
  have hstrict : (4 : ℝ) < (Fintype.card V : ℝ) / (G.indepNum : ℝ) := by
    rw [lt_div_iff₀ hαR]
    have : (4 : ℝ) * (G.indepNum : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast h
    linarith
  exact lt_of_lt_of_le hstrict (geomFrac_ge_ratio G hα)
