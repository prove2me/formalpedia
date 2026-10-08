-- Prove2me | Theorems.Thm_WorstCaseEq_Identical_expCost_eq_collision
-- name    : WorstCaseEq.Identical.expCost_eq_collision
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:42.60889+00:00
-- url     : https://prove2.me/theorems/92f6698e-f1e5-4a8d-8c92-b7e9e04f5a92
-- title:
--   Proof of Theorem 3, PDF p. 5 — c_i = w_i + Σ_{k≠i} t_ik w_k
-- statement:
--   Let $n$ agents with traffics $w_1,\dots,w_n$ choose among $m$ identical links according to a mixed profile $p=(p_i^j)$, and let $c_i$ be the expected cost of agent $i$, the expected traffic on the link it picks. With the collision probabilities $t_{ik}=\sum_j p_i^jp_k^j$,
--   $$
--   c_i=w_i+\sum_{k\neq i}t_{ik}\,w_k ,
--   $$
--   since the expected contribution of agent $k$ to the link of agent $i$ is $t_{ik}w_k$.
--
--   In the proof of Theorem 3 this identity connects the collision probabilities of (7) with the bound (6) on $c_i$.
--
--   **Formalization Note** The identity holds for every mixed profile, not only at an equilibrium as the page uses it.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 5, proof of Theorem 3, display after (7)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

namespace WorstCaseEq.Identical

/-- Proof of Theorem 3, PDF p. 5: the expected cost of agent `i` is `c_i = w_i + ∑_{k ≠ i} t_ik w_k`. -/
theorem expCost_eq_collision {n m : ℕ} (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile (S := fun _ : Fin n => Fin m) p) :
    ∀ i, expCost w p i = w i + ∑ k ∈ Finset.univ.erase i, collisionProb p i k * w k := by sorry

end WorstCaseEq.Identical
