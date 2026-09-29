-- Prove2me | solution 1 for UnitDistance.tri_indepRatio
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:13:13.854206+00:00
-- url     : https://prove2.me/submissions/d43051f3-0f95-4e8a-a014-0a93919d26ef

-- Sol generated from Novelty/UnitDistanceGraph.lean
import Mathlib
import Definitions.Def_Novelty_UnitDistanceGraph

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

open UnitDistance



/-! ### The equilateral triangle -/


/-
All three pairwise distances of the equilateral triangle equal `1`.
-/
lemma triPoints_dist (a b : Fin 3) (h : a ≠ b) : dist (triPoints a) (triPoints b) = 1 := by
  fin_cases a <;> fin_cases b <;> simp +decide [ * ] at h⊢;
  all_goals unfold triPoints; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ]; all_goals norm_num [ div_pow ]

/-
The unit-distance graph of the equilateral triangle is the complete graph on `Fin 3`.
-/
lemma unitDistanceGraph_tri_eq_top : unitDistanceGraph triPoints = ⊤ := by
  ext a b; by_cases h : a = b <;> simp_all +decide [ unitDistanceGraph ] ;
  exact triPoints_dist a b h

/-
The independence number of the complete graph on a nonempty finite vertex set is `1`.
-/
lemma indepNum_top {V : Type*} [Fintype V] [Nonempty V] :
    (⊤ : SimpleGraph V).indepNum = 1 := by
  refine' le_antisymm _ _ <;> norm_num [ SimpleGraph.indepNum ];
  · refine' csSup_le' _;
    rintro n ⟨ s, hs ⟩;
    rcases hs with ⟨ hs₁, hs₂ ⟩;
    exact hs₂ ▸ Finset.card_le_one.2 fun x hx y hy => by have := hs₁ hx hy; aesop;
  · refine' le_csSup _ _;
    · exact ⟨ _, fun n hn => hn.choose_spec.2.symm ▸ Finset.card_le_univ _ ⟩;
    · exact ⟨ { Classical.arbitrary V }, by simp +decide [ SimpleGraph.isNIndepSet_iff ] ⟩

/-- The equilateral triangle unit-distance graph has independence number `1`. -/
lemma tri_indepNum : (unitDistanceGraph triPoints).indepNum = 1 := by
  rw [unitDistanceGraph_tri_eq_top]; exact indepNum_top



open UnitDistance in
theorem solution:
    ((unitDistanceGraph triPoints).indepNum : ℚ) / (Fintype.card (Fin 3) : ℚ) = 1 / 3 := by
  rw [tri_indepNum]; norm_num
