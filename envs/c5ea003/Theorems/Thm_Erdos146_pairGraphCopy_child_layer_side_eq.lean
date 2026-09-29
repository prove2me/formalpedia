-- Prove2me | Theorems.Thm_Erdos146_pairGraphCopy_child_layer_side_eq
-- name    : Erdos146.pairGraphCopy_child_layer_side_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:51:37.670864+00:00
-- url     : https://prove2.me/theorems/819d4c28-c6e7-4b49-815f-1eb00ac9cfa7
-- title:
--   A copy of the layered graph respects the sides
-- statement:
--   Structural fact about the layered graph $H$ of Section 6. The counterexample graph $H$ is built in layers (Section 6): starting from a layer $V_0$ of size $L_0$, each subsequent layer is $V_i = \binom{V_{i-1}}{2}$, and every vertex $\{a,b\} \in V_i$ is joined to its two parents $a, b \in V_{i-1}$. Fact 6.1 records that the result is connected, bipartite and 2-degenerate. In any copy of the layered graph inside the bipartite host, the children of a layer all land on the same side — the bipartite structure of $H$ is inherited by every embedding, which is what lets the entropy potential be tracked layer by layer.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L16904-L16974

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.InformationTheory.Hamming

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairGraphCopy_child_layer_side_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : PairLayer baseSize (layer + 1)) :
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer second)).val.1 := by sorry
