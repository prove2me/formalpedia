-- Prove2me | Theorems.Thm_WorstCaseEq_Identical_socialCost_eq_sum_contrib
-- name    : WorstCaseEq.Identical.socialCost_eq_sum_contrib
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:27.730912+00:00
-- url     : https://prove2.me/theorems/cb6fd6f0-7e6c-4e9c-b1fa-364a643187ae
-- title:
--   Proof of Theorem 3, PDF p. 5 — cost = Σ_i q_i w_i
-- statement:
--   Let $n$ agents with traffics $w_1,\dots,w_n$ choose among $m\ge1$ identical links according to a profile $p=(p_i^j)$, and let $\mathrm{cost}$ be the social cost (4), the expected maximum link load. For each pure assignment take the lexicographically first link of maximum load, and let the **contribution probability** $q_i$ of agent $i$ be the probability that agent $i$ is on that link. Then
--   $$
--   \mathrm{cost}=\sum_i q_i\,w_i .
--   $$
--
--   This identity, stated as evident in the proof of Theorem 3, rewrites the expected maximum as a weighted sum of per-agent probabilities, which is what makes the pairwise argument of that proof possible.
--
--   **Formalization Note** The identity holds outcome by outcome, so it is stated for every real array $p$, without requiring the $p_i$ to be probability distributions. The tie-breaking rule (the lowest-indexed maximum link) is the paper's.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 5, proof of Theorem 3, first paragraph

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

namespace WorstCaseEq.Identical

/-- Proof of Theorem 3, PDF p. 5: the social cost is `∑_i q_i w_i`, where `q_i` is the probability that
agent `i` is on the lexicographically first link of maximum load. -/
theorem socialCost_eq_sum_contrib {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) :
    socialCost w p = ∑ i, contribProb w p i * w i := by sorry

end WorstCaseEq.Identical
