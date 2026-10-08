-- Prove2me | Theorems.Thm_WorstCaseEq_Speeds_eq8_linkCost
-- name    : WorstCaseEq.Speeds.eq8_linkCost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:11:32.852991+00:00
-- url     : https://prove2.me/theorems/cd5f7fb3-39bf-4a29-8f76-dbb8c9094f22
-- title:
--   (8), PDF p. 6 — the cost to agent i of link j is c_i^j = (M^j + (1 − p_i^j)w_i)/s_j
-- statement:
--   Consider $n$ agents with traffic $w_1,\dots,w_n$ on $m$ parallel links with speeds $s_1,\dots,s_m$, and let $p$ be a mixed profile in which every $p_k=(p_k^1,\dots,p_k^m)$ is a probability distribution. Fix an agent $i$ and a link $j$, and let agent $i$ place its traffic on link $j$ with certainty while every other agent keeps its mixed strategy. Then the expected delay of agent $i$ equals
--   $$
--   c_i^j=\frac{w_i+\sum_{k\neq i}p_k^j w_k}{s_j}=\frac{M^j+(1-p_i^j)\,w_i}{s_j},
--   $$
--   where $M^j=\sum_k p_k^j w_k$ is the expected traffic on link $j$.
--
--   This is the speed version of (2): the expected cost of a pure deviation of one agent is an explicit linear expression in the other agents' probabilities, which is what makes the equilibria computable in closed form.
--
--   **Formalization Note** The pure deviation is the profile in which agent $i$'s distribution is replaced by the point mass on $j$; its expected cost is minus the expected payoff of the published `agt_games` vocabulary. No positivity of speeds or traffic is needed for the identity, so none is assumed.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 6, (8); PDF p. 3, (2)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem eq8_linkCost {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile p) :
    ∀ i j, -AGT.expectedPayoff (payoff w s) (Function.update p i (WorstCaseEq.Identical.pureLottery j)) i
        = linkCost w s p i j ∧
      linkCost w s p i j = (WorstCaseEq.Identical.expTraffic w p j + (1 - p i j) * w i) / s j := by sorry

end WorstCaseEq.Speeds
