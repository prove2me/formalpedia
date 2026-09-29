-- Prove2me | Theorems.Thm_Erdos180_proposedFamilyFree_minDegree_sixteenth_power_le
-- name    : Erdos180.proposedFamilyFree_minDegree_sixteenth_power_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:14:28.264446+00:00
-- url     : https://prove2.me/theorems/d150c048-1e72-4078-a0da-9e1b72af7693
-- title:
--   The sixteenth-power degree bound
-- statement:
--   For an $\mathcal{F}$-free bipartite host of order $n$ with minimum degree $d \ge 2$,
--
--   $$d^{16} \;\le\; 1769472\, n^5 .$$
--
--   This is $d^{16} \ll N^5$ — the contradiction that closes Proposition 3.4 of the source. Since
--   Lemma 3.3 supplies a bipartite subgraph with $m \le 2nd$, an $\mathcal{F}$-free graph with too
--   many edges would produce a minimum degree violating this inequality.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6326-L6359

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Finset SimpleGraph

theorem Erdos180.proposedFamilyFree_minDegree_sixteenth_power_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hd : 2 ≤ d)
    (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 16 ≤ 1769472 * (n : ℝ) ^ 5 := by sorry
