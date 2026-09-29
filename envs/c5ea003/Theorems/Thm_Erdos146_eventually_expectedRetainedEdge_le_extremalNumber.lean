-- Prove2me | Theorems.Thm_Erdos146_eventually_expectedRetainedEdge_le_extremalNumber
-- name    : Erdos146.eventually_expectedRetainedEdge_le_extremalNumber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:53:53.61278+00:00
-- url     : https://prove2.me/theorems/fc321233-0fd3-4846-baaf-56d907c3b2f5
-- title:
--   The expected retained edge count bounds the extremal number from below
-- statement:
--   Step in assembling the lower bound of Theorem 1.2 from the sampled host: a graph that is $H$-free with probability $1 - o(1)$ (Proposition 8.1) and has $\Omega(n^{3/2+\varepsilon})$ edges by a second-moment argument witnesses $\mathrm{ex}(n, H) \ge c\,n^{3/2+\varepsilon}$. Eventually the expected retained edge count is a lower bound for $\mathrm{ex}(n, H)$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L18064-L18123

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

open Classical in
theorem Erdos146.eventually_expectedRetainedEdge_le_extremalNumber :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        hammingExpectedRetainedEdgeCount dimension
            (manuscriptHammingRadius dimension) / 2 ≤
          (SimpleGraph.extremalNumber
            (manuscriptVertexCount dimension)
            (pairGraphOverFin baseSize depth) : ℝ) := by sorry
