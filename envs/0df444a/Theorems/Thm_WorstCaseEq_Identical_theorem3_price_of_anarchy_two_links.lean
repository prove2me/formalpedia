-- Prove2me | Theorems.Thm_WorstCaseEq_Identical_theorem3_price_of_anarchy_two_links
-- name    : WorstCaseEq.Identical.theorem3_price_of_anarchy_two_links
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:59.84466+00:00
-- url     : https://prove2.me/theorems/ae2b52c8-8b29-4c40-ac58-e19e29946a82
-- title:
--   Theorem 3, PDF p. 5 — on m = 2 identical links every Nash equilibrium has social cost ≤ (3/2)·opt
-- statement:
--   Let $n$ agents with positive traffics $w_1,\dots,w_n$ each send their traffic over one of two identical parallel links, choosing the link at random with probabilities $p_i^1,p_i^2$, independently of each other. Let $p$ be a Nash equilibrium: no agent can lower its expected cost, the expected traffic on the link it uses, by changing its probabilities unilaterally. Let
--   $$
--   \mathrm{cost}=\sum_{j_1=1}^{2}\cdots\sum_{j_n=1}^{2}\prod_{i=1}^n p_i^{j_i}\,\max_{j=1,2}\sum_{k:\,j_k=j}w_k
--   $$
--   be the social cost, the expected maximum traffic over the two links, and let $\mathrm{opt}$ be the least maximum link traffic over all assignments of the agents to the links. Then
--   $$
--   \mathrm{cost}\ \le\ \frac32\,\mathrm{opt}.
--   $$
--
--   This is Theorem 3 of the paper: the price of anarchy (coordination ratio) for any number of agents and two identical links is at most $3/2$. Together with the instance of Theorem 1 (two unit agents, each uniform over the two links), which attains $3/2$, it determines the price of anarchy on two identical links exactly.
--
--   **Formalization Note** "The price of anarchy is at most $3/2$" (a bound on $\max\,\mathrm{cost}/\mathrm{opt}$ over equilibria) is stated as the inequality $\mathrm{cost}\le\tfrac32\,\mathrm{opt}$ for every equilibrium, which avoids a quotient with $\mathrm{opt}=0$. Positive traffics are part of the paper's model. The equilibrium is the full mixed Nash condition of the published `agt_games` vocabulary, payoffs being minus costs. Links are `Fin 2`; $n=0$ is allowed and then both sides are $0$.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 5, Theorem 3 (proof concluded on PDF p. 6)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

namespace WorstCaseEq.Identical

/-- Theorem 3, PDF p. 5: for any number of agents and `m = 2` identical links, every Nash equilibrium has
social cost (expected maximum link traffic) at most `3/2` times the optimum. -/
theorem theorem3_price_of_anarchy_two_links {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (p : Fin n → Fin 2 → ℝ) (hp : IsNash w p) :
    socialCost w p ≤ (3 / 2 : ℝ) * opt 2 w := by sorry

end WorstCaseEq.Identical
