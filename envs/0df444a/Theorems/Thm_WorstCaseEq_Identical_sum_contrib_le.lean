-- Prove2me | Theorems.Thm_WorstCaseEq_Identical_sum_contrib_le
-- name    : WorstCaseEq.Identical.sum_contrib_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:37.166747+00:00
-- url     : https://prove2.me/theorems/e41dc2ec-e429-4796-9b3d-509e7981f7a8
-- title:
--   Proof of Theorem 3, PDF p. 5 — on two links, Σ_{k≠i} q_k w_k ≤ (3/2 − q_i) Σ_{k≠i} w_k at every equilibrium
-- statement:
--   Let $n$ agents with positive traffics $w_1,\dots,w_n$ share two identical links, let $p$ be a Nash equilibrium, and let $q_k$ be the contribution probability of agent $k$ (the probability that it is on the lexicographically first link of maximum load). Then for every agent $i$,
--   $$
--   \sum_{k\neq i}q_k\,w_k\ \le\ \Big(\frac32-q_i\Big)\sum_{k\neq i}w_k .
--   $$
--
--   The proof of Theorem 3 obtains this by combining (7), the collision form of $c_i$ and the bound (6) for $m=2$; together with $\mathrm{cost}=\sum_k q_kw_k$ and $\mathrm{opt}\ge\max\{\tfrac12\sum_kw_k,w_i\}$ it yields the $\tfrac32$ bound.
--
--   **Formalization Note** The two links are indexed by `Fin 2`. Positive traffics are part of the paper's model.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 5, proof of Theorem 3, last display

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

namespace WorstCaseEq.Identical

/-- Proof of Theorem 3, PDF p. 5: on two identical links, at every Nash equilibrium and for every agent
`i`, `∑_{k ≠ i} q_k w_k ≤ (3/2 - q_i) ∑_{k ≠ i} w_k`. -/
theorem sum_contrib_le {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → Fin 2 → ℝ)
    (hp : IsNash w p) :
    ∀ i, ∑ k ∈ Finset.univ.erase i, contribProb w p k * w k ≤
      (3 / 2 - contribProb w p i) * ∑ k ∈ Finset.univ.erase i, w k := by sorry

end WorstCaseEq.Identical
