-- Prove2me | Theorems.Thm_MarkovEntanglement_multi_agent_decomposition_error_local_transition
-- name    : MarkovEntanglement.multi_agent_decomposition_error_local_transition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T01:24:58.190974+00:00
-- url     : https://prove2.me/theorems/90942b06-b1fa-4bb9-aec4-24a8c1664f7a
-- title:
--   Markov entanglement bounds the decomposition error against the marginalized local value functions
-- statement:
--   **Theorem 6 (Chen and Peng, p. 22), stated with $Q^\pi_i$ the value function of the marginalized local chain.**
--
--   Consider an $N$-agent MDP $\mathcal{M}_{1:N}$ and a policy $\pi : S \to \Delta(A)$, with discount factor $\gamma \in [0,1)$, local rewards bounded by $r^i_{\max}$, and occupancy measure $\mu^\pi_{1:N}$ strictly positive and stationary for $P^\pi_{1:N}$.
--
--   For each agent $i$, let $P^\pi_i$ denote the local (marginalized) transition induced by $P^\pi_{1:N}$ and $\mu^\pi_{1:N}$ through Eq. (2), and let $Q^\pi_i$ be the Q-value of $P^\pi_i$ under the local reward $r_i$. Let $\mathcal{E}_i(P^\pi_{1:N})$ be the measure of Markov entanglement of agent $i$ with respect to the $\mu^\pi_{1:N}$-weighted agent-wise total variation distance, attained at the local transition $P_i$. Then
--
--   $$\Bigl\| \, Q^\pi_{1:N}(s,a) - \sum_{i=1}^{N} Q^\pi_i(s_i,a_i) \, \Bigr\|_{\mu^\pi_{1:N}} \;\le\; \frac{4\gamma \sum_{i=1}^{N} \mathcal{E}_i\bigl(P^\pi_{1:N}\bigr)\, r^i_{\max}}{(1-\gamma)^2}.$$
--
--   ## Notes
--
--   Here $Q^\pi_i$ solves the Bellman equation of $P^\pi_i$, the chain of Eq. (2), which is the $Q^\pi_i$ appearing in the paper's statement. It is a different object from the Q-value of the entanglement-attaining $P_i$: the two chains are compared by the first part of Theorem 6, $\|P^\pi_i - P_i\|_{\mu_i,\infty} \le 2\mathcal{E}_i$.
--
--   The constant $4\gamma$ is attained. The proof splits the error at the tensor product $\bigotimes_i P_i$, contributing $2\gamma$, and crosses from $P_i$ to $P^\pi_i$, contributing a further $2\gamma$ — legs (I) and (II) of the argument on pp. 39-40.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Theorem 6, p. 22; proof legs (I) and (II) on pp. 39-40; local transition Eq. (2); local stationary distribution via Lemma 5, pp. 38-39

import Mathlib
import Definitions.Def_markov_entanglement_multi_atv

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem multi_agent_decomposition_error_local_transition
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl Ptrue : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |r i s| ≤ rmax i)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hopt : ∀ i, muAgentTVDistN i μ P (Pl i) = entanglementN i μ P)
    (hPtrue : ∀ i, IsTransitionMatrix (Ptrue i))
    (htrue : ∀ i, IsLocalTransitionN i P μ (Ptrue i))
    (hQi : ∀ i, IsBellmanQ (Ptrue i) (r i) γ (Qi i)) :
    muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
      ≤ 4 * γ * (∑ i, entanglementN i μ P * rmax i) / (1 - γ) ^ 2 := by
  sorry

end MarkovEntanglement
