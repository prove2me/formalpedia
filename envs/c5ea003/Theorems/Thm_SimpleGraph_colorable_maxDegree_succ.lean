-- Prove2me | Theorems.Thm_SimpleGraph_colorable_maxDegree_succ
-- name    : SimpleGraph.colorable_maxDegree_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:33:44.021091+00:00
-- url     : https://prove2.me/theorems/e1e92c35-4887-46eb-957f-02a573aa877c
-- title:
--   Greedy colouring bound.
-- statement:
--   **Greedy colouring bound.**  Every finite graph is colourable with `maxDegree + 1`
--   colours.
--
--   ```lean
--   theorem SimpleGraph.colorable_maxDegree_succ(G : SimpleGraph V) [DecidableRel G.Adj] :
--       G.Colorable (G.maxDegree + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GreedyDegreeColoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GreedyDegreeColoring.lean#L34

-- Thm stub generated from Novelty/GreedyDegreeColoring.lean
import Mathlib

/-!
# Greedy colouring: a finite graph is `(Δ+1)`-colourable

The classical greedy bound `χ(G) ≤ Δ(G) + 1` for the maximum degree `Δ(G)`.  We build a proper
colouring `V → Fin (maxDegree + 1)` by processing the vertices one at a time (induction on the
processed `Finset`), each time choosing a colour avoided by the already-considered neighbours.
Since every vertex has at most `maxDegree` neighbours, one of the `maxDegree + 1` colours is
always free.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the `1/(Δ+1)` independence-ratio floor is realised by a genuinely
constructive colouring, not merely an existence statement; greedy suffices.
Experiment (Experimenter): induct over the vertex set as a `Finset`; at each `insert v s`, the
colours used on `v`'s neighbours form a set of size `≤ degree v ≤ maxDegree`, so by pigeonhole
(`Finset.card_image_le` + a cardinality contradiction) `Fin (maxDegree+1)` has a free colour;
patch the previous colouring at `v` only.
Analysis (Analyst): correctness of the patch is local — recolouring `v` cannot break an edge
`{x,w}` with `x,w ≠ v`, and the freshly chosen colour is unequal to every neighbour's colour by
construction, in both orientations of the edge.
Critique (Critic): the only subtlety is edges incident to `v`; both `v–w` (new vs old) and
`x–v` (old vs new) are handled by the "free colour" property via `neighborFinset` symmetry.
Synthesis (PI): this constructive `(Δ+1)`-colouring is the engine that converts a bounded-degree
hypothesis into an independence-ratio floor `1/(Δ+1)`, and in particular `Δ ≤ 3 ⇒ i(G) ≥ 1/4`.
-- !-- end Lab Notes -- !--
-/

open Finset

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem SimpleGraph.colorable_maxDegree_succ(G : SimpleGraph V) [DecidableRel G.Adj] :
    G.Colorable (G.maxDegree + 1) := by sorry
