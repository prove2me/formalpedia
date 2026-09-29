-- Prove2me | Theorems.Thm_Erdos180_gammaBad_card_mul_fourpath_power_le
-- name    : Erdos180.gammaBad_card_mul_fourpath_power_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:13:32.355376+00:00
-- url     : https://prove2.me/theorems/9b163c2b-d923-4201-8d21-2841a6b633b8
-- title:
--   Polynomial bound on the number of bad vertices
-- statement:
--   Under the same hypotheses,
--
--   $$|U| \cdot \big(d(d-1)^3\big)^3 \cdot d \;\le\; 432\, n^5.$$
--
--   This is the explicit form of equation (7) of the source, $|U| \ll N^5/d^{13}$: the count
--   $|T_S| \le N^3/(6d)$ of independent triples with at least two common centres — which uses the
--   exclusion of $\mathcal{J}$ to make each third-base set $A_{yz}$ independent and hence of size at
--   most $N/d$ — is combined with the convexity lower bound for $C_u$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6094-L6154

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Erdos180.gammaBad_card_mul_fourpath_power_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (gammaBadVertices host).card *
      (d * (d - 1) ^ 3) ^ 3 * d ≤ 432 * n ^ 5 := by sorry
