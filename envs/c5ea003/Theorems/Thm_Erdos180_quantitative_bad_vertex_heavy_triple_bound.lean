-- Prove2me | Theorems.Thm_Erdos180_quantitative_bad_vertex_heavy_triple_bound
-- name    : Erdos180.quantitative_bad_vertex_heavy_triple_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:13:50.86895+00:00
-- url     : https://prove2.me/theorems/67f7feae-c285-498b-ba51-e1403e78a265
-- title:
--   The bad-vertex bound over the reals
-- statement:
--   The same estimate stated with real coefficients:
--
--   $$|U| \cdot \big(d(d-1)^3\big)^3 \cdot d \;\le\; 432\, n^5 .$$
--
--   Equation (7) of the source in the form in which the subsequent optimisation consumes it, so
--   that the exponents can be combined without integer-division artefacts.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6247-L6263

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Finset SimpleGraph

theorem Erdos180.quantitative_bad_vertex_heavy_triple_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
      432 * (n : ℝ) ^ 5 := by sorry
