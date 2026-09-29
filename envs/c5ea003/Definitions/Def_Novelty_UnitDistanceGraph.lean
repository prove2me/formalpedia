-- Prove2me | Definitions.Def_Novelty_UnitDistanceGraph
-- name    : Novelty_UnitDistanceGraph
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:25.176896+00:00
-- url     : https://prove2.me/theorems/7155ec88-15a9-4926-acd6-ea0cea9f9868
-- title:
--   Aether Catalog definitions — Novelty_UnitDistanceGraph
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UnitDistanceGraph`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UnitDistanceGraph.lean by skeleton subtraction
import Mathlib

/-!
# Unit-distance graphs in the Euclidean plane

A *unit-distance graph* is the graph induced by a set of points in `ℝ²` where two points are
adjacent exactly when they are at Euclidean distance `1`.  These graphs are the central
objects of the Hadwiger–Nelson problem and of Erdős's questions on the independence ratio of
the plane.

This file gives the basic definition together with the canonical worked example, the
**equilateral triangle**: three points pairwise at distance `1`.  Its induced unit-distance
graph is the complete graph `K₃`, whose independence number is `1`, so its independence ratio
is `1/3`.  Since `1/3 > 1/4`, the triangle does *not* witness the sub-`1/4` phenomenon — it is
the smallest concrete anchor for the ratio, and quantifies how far a single simplex is from
the conjectured threshold.

* `unitDistanceGraph` — the unit-distance graph of a point configuration `p : V → ℝ²`.
* `triPoints`, `triPoints_dist` — an explicit equilateral triangle with all three pairwise
  distances equal to `1`.
* `unitDistanceGraph_tri_eq_top` — its unit-distance graph is the complete graph on `Fin 3`.
* `indepNum_top` — the independence number of a complete graph on a nonempty finite vertex set
  is `1`.
* `tri_indepNum`, `tri_indepRatio` — the equilateral triangle has independence number `1` and
  independence ratio `1/3`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the equilateral triangle is a genuine planar unit-distance graph
and is exactly the complete graph `K₃`; its independence ratio is therefore `1/3`, a clean
rational strictly above the `1/4` threshold.
Experiment (Experimenter): place the three points at `(0,0)`, `(1,0)`, `(1/2, √3/2)` in
`EuclideanSpace ℝ (Fin 2)` and compute each pairwise distance via `EuclideanSpace.dist_eq`;
the `√3` terms collapse through `Real.sq_sqrt`.  Adjacency `≠ ∧ dist = 1` then reduces to `≠`,
identifying the graph with `⊤`.  The independence number is pinned by `IsIndepSet.card_le_indepNum`
(lower bound `1` via a singleton) and by the fact that any two distinct vertices of `⊤` are
adjacent (upper bound `1`).
Analysis (Analyst): the geometry is entirely finite and the only analytic input is
`(√3)² = 3`.  The value `1/3` shows the triangle is "off by a factor `4/3`" from the sub-`1/4`
regime; three separate simplices would still only give `1/3`, so a genuinely nontrivial planar
construction is required to break `1/4` — exactly the content of the open problem.
Critique (Critic): the result is not vacuous — the graph really is `⊤` (all pairs at unit
distance), and `indepNum = 1` uses that `Fin 3` is nonempty; on an empty vertex set the ratio
would be `0/0`.  The `Nonempty` hypothesis in `indepNum_top` is therefore load-bearing.
Synthesis (PI): this file supplies the concrete geometric side (a real planar unit-distance
graph and its exact independence ratio) that the combinatorial file
`IndependenceRatioChromatic` turns into a colouring lower bound.
-- !-- end Lab Notes -- !--
-/

open scoped Classical
open EuclideanSpace

namespace UnitDistance

/-- The **unit-distance graph** of a point configuration `p : V → ℝ²`: two distinct points are
adjacent iff they are at Euclidean distance exactly `1`. -/
def unitDistanceGraph {V : Type*} (p : V → EuclideanSpace ℝ (Fin 2)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ dist (p u) (p v) = 1
  symm := fun {u v} h => ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩


/-! ### The equilateral triangle -/

/-- Three points forming an equilateral triangle of side length `1`. -/
noncomputable def triPoints : Fin 3 → EuclideanSpace ℝ (Fin 2)
  | 0 => !₂[(0 : ℝ), 0]
  | 1 => !₂[(1 : ℝ), 0]
  | 2 => !₂[(1 : ℝ) / 2, Real.sqrt 3 / 2]

/-
All three pairwise distances of the equilateral triangle equal `1`.
-/

/-
The unit-distance graph of the equilateral triangle is the complete graph on `Fin 3`.
-/

/-
The independence number of the complete graph on a nonempty finite vertex set is `1`.
-/



end UnitDistance


