-- Prove2me | Theorems.Thm_Erdos180_gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
-- name    : Erdos180.gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:13:13.434923+00:00
-- url     : https://prove2.me/theorems/ea8a38fd-d9d0-4622-95dd-0039ca29c0a7
-- title:
--   Bad vertices are charged to ordered theta triples
-- statement:
--   For an $\mathcal{F}$-free bipartite host of order $n$ and minimum degree $d$, writing
--   $p = d(d-1)^3$ and $\theta$ for the heavy four-path threshold,
--
--   $$|U| \cdot \frac{\theta^2 p}{54} \;\le\; 2 \cdot \#\{\text{ordered theta triples}\}.$$
--
--   This is the double-counting identity at the heart of Proposition 3.4. Each $u \in U$ satisfies
--   $C_u = \sum_{T \ni u} (r(T) - 1)$ where $T$ ranges over independent triples with $u \in L(T)$,
--   and every such $T$ has $r(T) = 2$ exactly because $u$ is not a centre of any $S_3$; hence
--   $\sum_{u \in U} C_u \le 2|T_S|$. The left-hand side is the convexity lower bound
--   $C_u \gg d^{12}/N^2$ made explicit.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6054-L6092

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Erdos180.gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        (fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54) ≤
      2 * (orderedThetaTripleCount host : ℝ) := by sorry
