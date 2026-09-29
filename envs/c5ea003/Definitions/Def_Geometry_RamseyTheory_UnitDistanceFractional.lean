-- Prove2me | Definitions.Def_Geometry_RamseyTheory_UnitDistanceFractional
-- name    : Geometry_RamseyTheory_UnitDistanceFractional
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:52:48.050233+00:00
-- url     : https://prove2.me/theorems/5ed225c0-a20f-43f6-9e8a-4aefae91f97d
-- title:
--   Aether Catalog definitions — Geometry_RamseyTheory_UnitDistanceFractional
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.RamseyTheory.UnitDistanceFractional`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/RamseyTheory/UnitDistanceFractional.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_GeomFractionalChromatic
/-
Copyright (c) 2026. All rights reserved.

# Unit-distance graphs and the fractional-chromatic engine

This file supplies the *geometric payload* for the independence-ratio engine of
`GeomFractionalChromatic.lean`, in the spirit of Matolcsi–Ruzsa–Varga–Zsámboki
(`MRVZ`), de Grey (`deGrey`) and Erdős (`Er87`).

We define the **unit-distance graph** on a finite family of points of the
Euclidean plane, characterise its independent sets geometrically, and connect it
to the LP lower bound `geomFrac G ≥ |V| / α(G)`.

## Main results

* `unitDistanceGraph` — the unit-distance graph of `p : V → ℝ²`.
* `unitDistanceGraph_adj_iff` / `isIndepSet_iff_no_unit` — the geometric reading:
  an independent set is a set of points with **no two at distance exactly `1`**.
* `equilateral` — a concrete equilateral triangle whose three vertices are
  pairwise at distance `1`; its unit-distance graph is complete, so its geometric
  fractional chromatic number is exactly `3` (`geomFrac_equilateral`).  This is the
  small-scale analogue of the `MRVZ` graph `G_27`, whose value is exactly `4`.
* `geomFrac_top_fin5_gt_four` — a concrete graph reaching the strict regime
  `geomFrac > 4`, showing the engine's conclusion is attainable.
* `exists_geomFrac_gt_four_of_low_indep_ratio` — **the MRVZ reduction as a bridge
  theorem**: the existence of *any* finite graph with independence ratio `< 1/4`
  yields a graph with geometric fractional chromatic number `> 4`.  Combined with a
  unit-distance realisation, this is precisely the statement that the fractional
  chromatic number of the plane exceeds `4`.
-/
open SimpleGraph Finset GeomFrac
open scoped BigOperators

namespace UnitDistance

/-- A point of the Euclidean plane from its two coordinates. -/
noncomputable def pt (a b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![a, b]

/-- The **unit-distance graph** of a family of points `p`: two distinct vertices are
adjacent iff their points are at Euclidean distance exactly `1`. -/
noncomputable def unitDistanceGraph {V : Type*} (p : V → EuclideanSpace ℝ (Fin 2)) :
    SimpleGraph V where
  Adj u v := u ≠ v ∧ dist (p u) (p v) = 1
  symm := by
    rintro u v ⟨h1, h2⟩
    exact ⟨h1.symm, by rw [_root_.dist_comm]; exact h2⟩
  loopless := ⟨fun u hu => hu.1 rfl⟩



/-! ### A concrete equilateral triangle -/

/-- The three vertices of a unit equilateral triangle. -/
noncomputable def equilateral : Fin 3 → EuclideanSpace ℝ (Fin 2)
  | 0 => pt 0 0
  | 1 => pt 1 0
  | 2 => pt (1 / 2) (Real.sqrt 3 / 2)







/-! ### The strict `> 4` regime -/




end UnitDistance

/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  Two bold claims: (1) the unit equilateral triangle
already realises the *tightness* phenomenon of the `MRVZ` engine — its geometric
fractional chromatic number should be exactly `3`, mirroring `G_27`'s exact `4`;
(2) the entire "plane `> 4`" reduction is a one-line consequence of the engine once a
graph with independence ratio `< 1/4` is in hand.

**Experiment (Experimenter).**  We built `unitDistanceGraph`, computed the three
equilateral distances in `EuclideanSpace ℝ (Fin 2)` via `EuclideanSpace.dist_eq` and
`Real.sq_sqrt` (the `√3/2` height reduces to `nlinarith`), and proved the triangle is
complete (`equilateral_adj_iff`, by `fin_cases`).  Hence `α = 1`, `|V| = 3`, and the
engine pins `geomFrac = 3` between the singleton upper bound and the ratio lower bound.
The strict `> 4` regime is realised concretely by `K₅` and abstractly by the bridge
theorem.

**Analysis (Analyst).**  Equilateral triangle: `geomFrac = |V|/α = 3`, exact because
`K_n` is vertex-transitive.  The obstruction to a *unit-distance* `> 4` example is
real: planar unit-distance graphs have large independent sets, so `4·α < |V|` fails
for every small unit-distance graph — this is exactly why `MRVZ` need `27`+`2`
vertices and a computer search.  `K₅` shows the engine's target value is attainable in
the abstract, isolating the difficulty as purely geometric (finding a *plane*
realisation with small independence ratio).

**Critique (Critic).**  No theorem is vacuous: `geomFrac_equilateral` computes an exact
real number via `le_antisymm`; `geomFrac_top_fin5_gt_four` uses the engine plus a real
strict inequality; the bridge theorem is a clean existential reduction, not a tautology
(its hypothesis fails for bipartite graphs).  The distance computations are honest
Euclidean-norm facts, not `decide`.  What we have **not** done — and honestly cannot at
this scale — is exhibit the `29`-vertex *unit-distance* witness itself; that requires
explicit coordinates and a large independence-number computation, recorded as a bold
future direction.

**Synthesis (PI).**  The geometry (distance computations, independence characterisation)
plugs directly into the domain-free engine.  The remaining gap is exactly the
`MRVZ` construction of a plane realisation with independence ratio `< 1/4`.
-/


