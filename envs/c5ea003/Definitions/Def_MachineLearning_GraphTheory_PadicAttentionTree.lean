-- Prove2me | Definitions.Def_MachineLearning_GraphTheory_PadicAttentionTree
-- name    : MachineLearning_GraphTheory_PadicAttentionTree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:42:17.382636+00:00
-- url     : https://prove2.me/theorems/f6965878-0a48-4e05-8aac-9fcf14cc54a0
-- title:
--   Aether Catalog definitions — MachineLearning_GraphTheory_PadicAttentionTree
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.GraphTheory.PadicAttentionTree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/GraphTheory/PadicAttentionTree.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# p-adic Compression of Attention into Hierarchical Trees

This file formalizes the *non-Archimedean (ultrametric) compression* of attention
score matrices into **hierarchical trees**, the geometric substrate of the
"Renormalization Fixed Points in Transformer In-Context Learning via p-adic
Attention" program.

An attention row, once summarized by a p-adic valuation, lives in an ultrametric
space. The defining property that turns such a summary into a *tree* is that
ultrametric balls are **nested or disjoint** — there is no partial overlap, so the
collection of balls at all scales forms a rooted hierarchy (a dendrogram). We then
show the induced *same-cluster* relation is, at every scale `ε ≥ 0`, an equivalence
relation whose classes are exactly the closed balls, and that decreasing `ε`
*refines* the partition. This is precisely the hierarchical-tree compression
asserted by the conjecture, proven for an arbitrary ultrametric space and hence for
`ℚ_[p]` (`Padic.instIsUltrametricDist`).

## Catalog synthesis

This **extends** `MachineLearning/Attention.lean` (linear/scalar attention as a
natural transformation) by replacing the *Archimedean* (Euclidean) view of
attention with a *non-Archimedean* one, and it shares the ultrametric backbone of
`MachineLearning/UltrametricKLDivergence.lean` (`padicNormDivergence`,
`ultrametric_div_isosceles`). Where that file builds a *divergence* on `ℚ_[p]`, here
we build the *tree* structure on a general ultrametric space, of which `ℚ_[p]` is the
canonical instance.

## Main results

* `ultrametric_balls_subset_of_le` — two closed balls with `r ≤ s` that meet satisfy
  the small ⊆ large containment.
* `ultrametric_balls_nested_or_disjoint` — the tree property: any two closed balls
  (with comparable radii) are nested or disjoint.
* `clusterSetoid` — the same-cluster relation at scale `ε ≥ 0` is an equivalence.
* `cluster_eq_closedBall` — cluster classes are exactly closed balls.
* `sameCluster_mono` — coarsening: classes only grow as the scale `ε` grows
  (equivalently, the partition refines as `ε` shrinks) — the levels of the tree.
-/


open Metric

namespace PadicAttn

variable {S : Type*} [PseudoMetricSpace S] [IsUltrametricDist S]

/-! ## The hierarchical tree property of ultrametric attention summaries -/

-- !-- Lab Notebook -- !--
-- Hypothesis: p-adic compression of attention rows yields a *tree* iff the balls
--   of the summary space never partially overlap.
-- Result: proved (`ultrametric_balls_nested_or_disjoint`) for any ultrametric space,
--   hence for ℚ_[p]; the strong (isosceles) triangle inequality is the only input.
-- Insight: the entire dendrogram structure is a consequence of a single inequality
--   `dist x z ≤ max (dist x y) (dist y z)` — no probabilistic or learned structure
--   is needed for the hierarchy to exist; it is forced by non-Archimedean geometry.
-- Failure analysis: a first attempt via `‖·‖` and `ring` failed (`ring` does not
--   normalise group subtraction); switching to the `dist` API and
--   `IsUltrametricDist.dist_triangle_max` removed all friction.
-- !-- Lab Notebook -- !--

-- !-- If the closed ball of radius `r` and the (no-smaller) closed ball of radius `s`
-- share a point `z`, then for any `w` in the small ball, `dist w y ≤ s` via two
-- applications of the ultrametric inequality through `z`. -- !--

-- !-- Either the balls share a point (then nested, by the previous lemma) or their
-- intersection is empty (then disjoint). -- !--

/-! ## Same-cluster relation: the levels of the tree -/

/-- Two attention summaries are in the same cluster at resolution `ε` when their
    ultrametric distance is at most `ε`. -/
def SameCluster (ε : ℝ) (x y : S) : Prop := dist x y ≤ ε



-- !-- Transitivity is exactly the ultrametric inequality: `dist x z ≤ max (dist x y)
-- (dist y z) ≤ max ε ε = ε`. This is where non-Archimedean geometry is essential —
-- it would FAIL for an ordinary metric. -- !--



-- !-- A cluster class is, by unfolding both definitions and using `dist_comm`, exactly
-- a closed ball; the tree-property lemma above therefore governs the clusters. -- !--


end PadicAttn


