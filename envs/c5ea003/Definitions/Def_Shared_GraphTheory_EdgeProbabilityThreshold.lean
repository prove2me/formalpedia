-- Prove2me | Definitions.Def_Shared_GraphTheory_EdgeProbabilityThreshold
-- name    : Shared_GraphTheory_EdgeProbabilityThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:53:52.267712+00:00
-- url     : https://prove2.me/theorems/0bf53eb1-6613-4bd9-a820-95f83ce3c8f9
-- title:
--   Aether Catalog definitions — Shared_GraphTheory_EdgeProbabilityThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.GraphTheory.EdgeProbabilityThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/GraphTheory/EdgeProbabilityThreshold.lean by skeleton subtraction
import Mathlib

/-! # Edge-probability thresholds for graphs without isolated vertices

For a finite simple graph with `m` edges and `n` non-isolated vertices, this
file establishes the basic constraints on the ratio `n.choose 2 / m` appearing
in the proposed probability threshold.  The results form a chain: the closed
formula for `n.choose 2` gives positivity, the universal simple-graph edge
bound gives the lower endpoint `1`, and the handshake lemma gives the upper
endpoint `n - 1` when every vertex is non-isolated.
-/

open Finset SimpleGraph

namespace EdgeProbabilityThreshold

/-- The real-valued ratio between the number of possible pairs and the number
of actual edges. -/
noncomputable def threshold (n m : ℕ) : ℝ := (n.choose 2 : ℝ) / m

/-
The usual closed form for the number of unordered pairs, stated over the
reals to avoid truncated natural-number division.
-/

/-
The pair count is positive as soon as there are at least two vertices.
-/

/-
Any positive denominator bounded by the number of available pairs gives a
threshold at least one.
-/

/-
A probability strictly below the threshold satisfies the equivalent
cross-multiplied edge-budget inequality.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-
If every vertex is non-isolated, the handshake identity forces `n ≤ 2m`.
-/

/-
For a nonempty simple graph, its number of edges is at most the number of
unordered vertex pairs; consequently its threshold is at least one.
-/

/-
If all vertices are non-isolated, the threshold is at most `n - 1`.
Together with `graph_one_le_threshold`, this locates it in the sharp elementary
interval `[1,n-1]`.
-/

/-
The complete threshold interval for a graph with no isolated vertices.
-/

/-
The proposed strict threshold is automatic for every probability `p < 1`:
the lower endpoint of the interval is already one.  This is the central
contrarian consequence of the elementary edge-count bound.
-/

/-
Thus any `p` below the proposed ratio lies below `n - 1` and
obeys the cross-multiplied edge-budget inequality.
-/

end EdgeProbabilityThreshold


