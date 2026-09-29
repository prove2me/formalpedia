-- Prove2me | Theorems.Thm_MarkovEntanglement_separable_value_decomposition_with_shared_state
-- name    : MarkovEntanglement.separable_value_decomposition_with_shared_state
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T13:54:07.984467+00:00
-- url     : https://prove2.me/theorems/ece0c9ae-b002-4f7d-ac73-2cbed46778f2
-- title:
--   Exact decomposition survives a shared global state
-- statement:
--   ## Statement
--
--   **Proposition.** Consider a Markov system in which the agents, besides their local
--   state-action pairs, share a global coordinate $z$. If the system is agent-wise separable for
--   every agent, then the value function decomposes exactly:
--   $$Q^\pi(s, a, z) \;=\; \sum_{i=1}^{N} Q^\pi_{i}(s_i, a_i, z).$$
--
--   ## Notes
--
--   Many practical systems are not products of independent agents but share some common state —
--   a global clock, a shared resource level, a market price. This proposition says the exact
--   decomposition of Theorem 1 survives that generalisation, provided the local pieces are allowed
--   to depend on the shared coordinate as well.
--
--   Note where $z$ appears: each local value function $Q_i$ takes $z$ as an argument. The
--   decomposition is additive across agents but not independent of the shared state, which is
--   exactly what makes the model useful — the agents remain coupled through $z$ while the value
--   function stays a sum.
--
--   Search terms: shared global state multi-agent MDP, factored value function with common state,
--   agent-wise separability, contextual multi-agent decomposition.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Proposition 2, p. 45

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem separable_value_decomposition_with_shared_state
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (P : Matrix (JointZ S Z) (JointZ S Z) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (Q : JointZ S Z → ℝ)
    (r : ∀ i, S i × Z → ℝ)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p.1 i, p.2)) γ Q)
    (hsep : ∀ i, ∃ Pi : Matrix (S i × Z) (S i × Z) ℝ,
      ∀ p t, marginalZ i P p t = Pi (p.1 i, p.2) t) :
    ∃ Qi : ∀ i, S i × Z → ℝ, ∀ p : JointZ S Z, Q p = ∑ i, Qi i (p.1 i, p.2) := by
  sorry

end MarkovEntanglement
