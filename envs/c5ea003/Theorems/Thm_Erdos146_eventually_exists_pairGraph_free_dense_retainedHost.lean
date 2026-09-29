-- Prove2me | Theorems.Thm_Erdos146_eventually_exists_pairGraph_free_dense_retainedHost
-- name    : Erdos146.eventually_exists_pairGraph_free_dense_retainedHost
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:53:29.357442+00:00
-- url     : https://prove2.me/theorems/a17274f9-1dbb-4dfa-90e3-76d3eff02bdc
-- title:
--   Eventually there is a dense $H$-free retained host
-- statement:
--   Step in assembling the lower bound of Theorem 1.2 from the sampled host: a graph that is $H$-free with probability $1 - o(1)$ (Proposition 8.1) and has $\Omega(n^{3/2+\varepsilon})$ edges by a second-moment argument witnesses $\mathrm{ex}(n, H) \ge c\,n^{3/2+\varepsilon}$. For all sufficiently large $m$ the two events — freeness and density — hold simultaneously with positive probability, so such a host exists.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L17939-L18007

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.eventually_exists_pairGraph_free_dense_retainedHost :
    ∃ baseSize depth : ℕ,
      4 ≤ baseSize ∧
      0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) ∧
      ∀ᶠ dimension : ℕ in Filter.atTop,
        ∃ retained : Set (Bool × HammingWord dimension),
          (pairGraphOverFin baseSize depth).Free
              (retainedHammingHost dimension
                (manuscriptHammingRadius dimension) retained) ∧
          hammingRetainedVertexCount dimension retained <
            3 * hammingRetentionProbability dimension *
              ((2 ^ dimension : ℕ) : ℝ) ∧
          hammingExpectedRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) / 2 ≤
            hammingRetainedEdgeCount dimension
              (manuscriptHammingRadius dimension) retained := by sorry
