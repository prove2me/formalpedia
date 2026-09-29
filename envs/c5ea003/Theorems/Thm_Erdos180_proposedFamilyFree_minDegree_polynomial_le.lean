-- Prove2me | Theorems.Thm_Erdos180_proposedFamilyFree_minDegree_polynomial_le
-- name    : Erdos180.proposedFamilyFree_minDegree_polynomial_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:14:09.723662+00:00
-- url     : https://prove2.me/theorems/2f97c9fd-d3c7-43e0-9120-c5c918072edf
-- title:
--   Minimum degree against the order, polynomial form
-- statement:
--   For an $\mathcal{F}$-free bipartite host of order $n > 0$ with minimum degree $d$,
--
--   $$d^2 (d-1)^2 \big(d(d-1)^3\big)^3 \;\le\; 864\, n^5 .$$
--
--   This is the step of Proposition 3.4 that uses the exclusion of $\mathcal{K}$: since no edge can
--   have both endpoints outside $U$ — two copies of $S_3$ centred at its endpoints plus the edge
--   would form a member of $\mathcal{K}$ — the set $U$ is a vertex cover, so
--   $Nd \le 2e(B) \le 2|U|\Delta(B)$. With $\Delta(B) \ll N/d^2$ from Lemma 3.3 and the bad-vertex
--   bound this yields the displayed inequality.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6265-L6324

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Finset SimpleGraph

theorem Erdos180.proposedFamilyFree_minDegree_polynomial_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 ≤
      864 * (n : ℝ) ^ 5 := by sorry
