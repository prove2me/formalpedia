-- Prove2me | Theorems.Thm_WorstCaseEq_Speeds_nash_support_minimizes
-- name    : WorstCaseEq.Speeds.nash_support_minimizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:11:38.517866+00:00
-- url     : https://prove2.me/theorems/20f70f04-d7c9-4583-aab0-6d5168101a37
-- title:
--   PDF pp. 3, 6 — at a Nash equilibrium with speeds, each agent uses only links minimizing c_i^j, and c_i = min_j c_i^j
-- statement:
--   Consider $n$ agents with traffic $w_1,\dots,w_n$ on $m\ge 1$ parallel links with speeds $s_1,\dots,s_m$, and let $p$ be a Nash equilibrium. Write $c_i^j$ for the cost to agent $i$ of placing its traffic on link $j$ (see (8)) and $c_i$ for the expected cost of agent $i$ at $p$. Then:
--
--   1. agent $i$ assigns positive probability only to links that minimize $c_i^j$: if $p_i^j>0$ then $c_i^j\le c_i^{j'}$ for every link $j'$;
--   2. the expected cost of agent $i$ is the minimum link cost,
--   $$
--   c_i=\min_j c_i^j .
--   $$
--
--   This is the support characterization of equilibria on which the closed-form description of all Nash equilibria ((3) and (9)) rests.
--
--   **Formalization Note** The paper states this for identical links in §2 (PDF p. 3) and applies it with speeds in §3 ("We can estimate all Nash equilibria again", PDF p. 6). The statement holds for arbitrary real speeds and traffic, so no positivity is assumed; at least one link is required for the minimum to exist.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 3 (§2, support property and c_i = min_j c_i^j); PDF p. 6 (Links with different capacities)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem nash_support_minimizes {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (s : Fin m → ℝ)
    (p : Fin n → Fin m → ℝ) (hp : IsNash w s p) :
    (∀ i j, 0 < p i j → ∀ j', linkCost w s p i j ≤ linkCost w s p i j') ∧
      ∀ i, expCost w s p i = Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) := by sorry

end WorstCaseEq.Speeds
