-- Prove2me | Theorems.Thm_WorstCaseEq_Identical_nash_support_minimizes
-- name    : WorstCaseEq.Identical.nash_support_minimizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:39.107979+00:00
-- url     : https://prove2.me/theorems/80a1e8f5-82a1-4000-8eba-72ff81e211c7
-- title:
--   §2, PDF p. 3 — at a Nash equilibrium each agent uses only links minimizing c_i^j, and c_i = min_j c_i^j
-- statement:
--   Let $n$ agents with traffics $w_1,\dots,w_n$ share $m\ge1$ identical links, and let $p=(p_i^j)$ be a Nash equilibrium. For an agent $i$ and a link $j$ let $c_i^j=w_i+\sum_{k\neq i}p_k^jw_k$ be the cost of agent $i$ when its traffic is assigned to link $j$, as in (2). Then:
--
--   1. agent $i$ assigns positive probability only to links minimizing $c_i^j$: if $p_i^j>0$ then $c_i^j\le c_i^{j'}$ for every link $j'$;
--   2. the expected cost $c_i$ of agent $i$ equals the minimum link cost,
--   $$
--   c_i=\min_j c_i^j .
--   $$
--
--   This is the support description of equilibria in §2 of the paper. It justifies the paper's double use of $c_i$, as the expected cost and as $\min_j c_i^j$, which is how Theorem 2 is proved.
--
--   **Formalization Note** No sign condition on the traffics is needed. The minimum over links uses $m\ge1$.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 3, §2, paragraph after (2)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

namespace WorstCaseEq.Identical

/-- Support property, §2, PDF p. 3: at a Nash equilibrium agent `i` puts positive probability only on
links `j` minimizing `c_i^j`, and its expected cost equals `c_i = min_j c_i^j`. -/
theorem nash_support_minimizes {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : IsNash w p) :
    (∀ i j, 0 < p i j → ∀ j', linkCost w p i j ≤ linkCost w p i j') ∧
      ∀ i, expCost w p i = Finset.univ.inf' Finset.univ_nonempty (linkCost w p i) := by sorry

end WorstCaseEq.Identical
