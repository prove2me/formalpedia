-- Prove2me | Theorems.Thm_WorstCaseEq_Identical_eq2_linkCost
-- name    : WorstCaseEq.Identical.eq2_linkCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:34.073633+00:00
-- url     : https://prove2.me/theorems/da18efb4-f381-4309-96f5-c0f9d8ed1c35
-- title:
--   (2), PDF p. 3 — c_i^j = w_i + Σ_{k≠i} p_k^j w_k = M^j + (1 − p_i^j) w_i
-- statement:
--   Let $n$ agents with traffics $w_1,\dots,w_n$ share $m$ identical links, and let $p=(p_i^j)$ be a mixed profile: each $(p_i^1,\dots,p_i^m)$ is a probability distribution on the links. Write $M^j=\sum_i p_i^j w_i$ for the expected traffic on link $j$.
--
--   Fix an agent $i$ and a link $j$, and suppose agent $i$ sends its traffic on link $j$ with certainty while every other agent keeps its mixed strategy. Then the expected cost of agent $i$ (the expected traffic on link $j$) is
--   $$
--   c_i^j=w_i+\sum_{k\neq i}p_k^j w_k = M^j+(1-p_i^j)\,w_i .
--   $$
--
--   This is equation (2) of the paper. It turns the expected cost of a pure deviation into a closed form that is linear in the other agents' probabilities, and it is the starting point of the equilibrium characterization and of Theorem 2.
--
--   **Formalization Note** The first equality is stated for the expected cost in the profile in which agent $i$'s strategy is replaced by the point mass on $j$; the second equality is an algebraic identity. No sign condition on the traffics is needed.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 3, (2)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

namespace WorstCaseEq.Identical

/-- (2), PDF p. 3: for a mixed profile `p`, the expected cost of agent `i` when its own traffic is
assigned to link `j` (the others keeping their lotteries) is `c_i^j = w_i + ∑_{k ≠ i} p_k^j w_k`, and
`c_i^j = M^j + (1 - p_i^j) w_i`. -/
theorem eq2_linkCost {n m : ℕ} (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p) :
    ∀ i j, -AGT.expectedPayoff (S := fun _ : Fin n => Fin m) (payoff w)
        (Function.update p i (pureLottery j)) i = linkCost w p i j ∧
      linkCost w p i j = expTraffic w p j + (1 - p i j) * w i := by sorry

end WorstCaseEq.Identical
