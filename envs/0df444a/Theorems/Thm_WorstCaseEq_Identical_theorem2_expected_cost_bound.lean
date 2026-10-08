-- Prove2me | Theorems.Thm_WorstCaseEq_Identical_theorem2_expected_cost_bound
-- name    : WorstCaseEq.Identical.theorem2_expected_cost_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:22.88946+00:00
-- url     : https://prove2.me/theorems/fab06d2f-a179-44a1-8ebc-81cf2657119e
-- title:
--   Theorem 2, PDF pp. 4–5 — at every Nash equilibrium on m identical links, c_i ≤ Σ_k w_k/m + ((m − 1)/m) w_i ≤ (2 − 1/m) opt
-- statement:
--   Let $n$ agents with positive traffics $w_1,\dots,w_n$ share $m\ge1$ identical links, let $p$ be a Nash equilibrium, and let $c_i$ be the expected cost of agent $i$ at $p$ (the expected traffic on the link it picks). Let $\mathrm{opt}$ be the least maximum link load over all assignments of agents to links. Then for every agent $i$,
--   $$
--   c_i\ \le\ \frac{\sum_k w_k}{m}+\frac{m-1}{m}\,w_i \qquad (6)
--   $$
--   and
--   $$
--   c_i\ \le\ \Big(2-\frac1m\Big)\,\mathrm{opt}.
--   $$
--
--   This is Theorem 2 of the paper: the expected cost seen by every individual agent at any equilibrium is within a factor $2-1/m$ of the optimum, for any number of agents and links. The sharper bound (6) is used, for $m=2$, in the proof of Theorem 3.
--
--   **Formalization Note** Positive traffics are part of the paper's model. Both conclusions are stated for every agent.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF pp. 4–5, Theorem 2, (6)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

namespace WorstCaseEq.Identical

/-- Theorem 2 with (6), PDF pp. 4–5: on `m` identical links, at every Nash equilibrium the expected cost
of each agent `i` is at most `∑_k w_k / m + ((m - 1)/m) w_i`, and at most `(2 - 1/m)` times the optimum. -/
theorem theorem2_expected_cost_bound {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (p : Fin n → Fin m → ℝ) (hp : IsNash w p) :
    ∀ i, expCost w p i ≤ (∑ k, w k) / m + (((m : ℝ) - 1) / m) * w i ∧
      expCost w p i ≤ (2 - 1 / (m : ℝ)) * opt m w := by sorry

end WorstCaseEq.Identical
