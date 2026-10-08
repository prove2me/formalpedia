-- Prove2me | Theorems.Thm_WorstCaseEq_Identical_eq7_contrib_add_le
-- name    : WorstCaseEq.Identical.eq7_contrib_add_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:52.22582+00:00
-- url     : https://prove2.me/theorems/ed56637c-762b-4db8-8a42-3cea016d9d01
-- title:
--   (7), PDF p. 5 — q_i + q_k ≤ 1 + t_ik for distinct agents i, k
-- statement:
--   Let $n$ agents with traffics $w_1,\dots,w_n$ choose among $m\ge1$ identical links according to a mixed profile $p=(p_i^j)$, and let $q_i$ be the contribution probability of agent $i$ (the probability that it is on the lexicographically first link of maximum load). For two distinct agents $i\neq k$ let $t_{ik}=\sum_j p_i^jp_k^j$ be their collision probability, the probability that both are on the same link. Then
--   $$
--   q_i+q_k\ \le\ 1+t_{ik}. \qquad (7)
--   $$
--
--   Both agents can contribute to the social cost in the same outcome only if they collide. Inequality (7) is the pairwise bound at the heart of the proof of Theorem 3.
--
--   **Formalization Note** The page prints the inequality as "$q_i+q_l\le 1+t_{ik}$"; the index $l$ is a typo for $k$, and the statement here uses $k$. The page's "both agents $i$ and $k$" means distinct agents, and $i\neq k$ is a hypothesis: for $i=k$ the inequality can fail.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 5, (7) in the proof of Theorem 3

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

namespace WorstCaseEq.Identical

/-- (7), proof of Theorem 3, PDF p. 5: two distinct agents `i`, `k` can both contribute to the social
cost only if they collide, so `q_i + q_k ≤ 1 + t_ik`. -/
theorem eq7_contrib_add_le {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p) :
    ∀ i k, i ≠ k → contribProb w p i + contribProb w p k ≤ 1 + collisionProb p i k := by sorry

end WorstCaseEq.Identical
