-- Prove2me | Theorems.Thm_Erdos146_eventually_manuscriptExpectedRetainedEdge_entropy_lower
-- name    : Erdos146.eventually_manuscriptExpectedRetainedEdge_entropy_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:52:52.321707+00:00
-- url     : https://prove2.me/theorems/8703e485-1add-482c-b0a9-c6b5f93a61d2
-- title:
--   Eventual entropy lower bound on the expected retained edges
-- statement:
--   Step in assembling the lower bound of Theorem 1.2 from the sampled host: a graph that is $H$-free with probability $1 - o(1)$ (Proposition 8.1) and has $\Omega(n^{3/2+\varepsilon})$ edges by a second-moment argument witnesses $\mathrm{ex}(n, H) \ge c\,n^{3/2+\varepsilon}$. The expected retained edge count eventually exceeds the entropy-derived lower bound, which is where $C(\tau) = 2h(\tau) - 1$ enters.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L17696-L17754

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.eventually_manuscriptExpectedRetainedEdge_entropy_lower
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.exp
          ((dimension : ℝ) *
            (sampledHammingEdgeEntropyRate - loss)) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) := by sorry
