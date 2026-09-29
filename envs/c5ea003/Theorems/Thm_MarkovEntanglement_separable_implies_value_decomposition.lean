-- Prove2me | Theorems.Thm_MarkovEntanglement_separable_implies_value_decomposition
-- name    : MarkovEntanglement.separable_implies_value_decomposition
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T05:23:03.796714+00:00
-- url     : https://prove2.me/theorems/45b244b4-c4da-4f68-b161-6f5e5f89189d
-- title:
--   Separable transitions admit an exact value decomposition
-- statement:
--   ## Statement
--
--   **Theorem.** Consider an $N$-agent Markov system with joint transition matrix
--   $P^\pi_{1:N}$ on the product state-action space, discount factor $\gamma$, and rewards
--   that are a sum of local rewards, $r(s,a) = \sum_{i=1}^N r_i(s_i,a_i)$. Suppose the agents
--   are **separable**, that is, there are $K \in \mathbb{Z}^+$, coefficients $\{x_j\}_{j \in [K]}$
--   with $\sum_j x_j = 1$, and local transition matrices $\{P^{(j)}_i\}$ such that
--
--   $$P^\pi_{1:N} \;=\; \sum_{j=1}^{K} x_j\, P^{(j)}_1 \otimes P^{(j)}_2 \otimes \cdots \otimes P^{(j)}_N .$$
--
--   Let $Q$ be the solution of the Bellman equation $Q = r + \gamma P^\pi_{1:N} Q$. Then $Q$
--   decomposes exactly into local value functions:
--
--   $$Q(s,a) \;=\; \sum_{i=1}^{N} Q_i(s_i, a_i).$$
--
--   ## Notes
--
--   **Value decomposition** is the standard approximation in multi-agent dynamic programming
--   and reinforcement learning: replace the value of a joint state by a sum of per-agent
--   local values. It underlies index policies for restless multi-armed bandits and a range of
--   modern multi-agent RL architectures, but it is normally used as a heuristic.
--
--   This theorem identifies the exact structural condition under which the heuristic is not an
--   approximation at all but an identity: the joint transition matrix must be **separable**, a
--   finite affine combination of tensor products of local transitions. The name is deliberate —
--   separability here is the direct analogue of separability of a quantum state, and its
--   failure is what the paper calls *Markov entanglement*.
--
--   The converse direction, and the quantitative version that bounds the decomposition error
--   when separability fails, are the other results of this mission. Searchers looking for
--   "when does value decomposition work", "additive value function", "separable transition
--   kernel" or "tensor product of transition matrices" should land here.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Theorem 1, p. 9

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem separable_implies_value_decomposition
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P) (hsep : IsSeparableN P)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q) :
    ∃ Qi : ∀ i, S i → ℝ, IsValueDecomposition Q Qi := by
  sorry

end MarkovEntanglement
