-- Prove2me | Theorems.Thm_MarkovEntanglement_multi_agent_decomposition_error
-- name    : MarkovEntanglement.multi_agent_decomposition_error
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T13:55:32.619587+00:00
-- url     : https://prove2.me/theorems/521a428f-cf37-4773-bce2-084f23c09560
-- title:
--   Markov entanglement bounds the multi-agent value decomposition error
-- statement:
--   ## Statement
--
--   **Theorem.** Consider an $N$-agent MDP $\mathcal{M}_{1:N}$ and a policy
--   $\pi : S \to \Delta(A)$, with discount factor $\gamma \in [0,1)$, local rewards bounded by
--   $r^i_{\max}$, and occupancy measure $\mu^\pi_{1:N}$ stationary for the joint transition
--   $P^\pi_{1:N}$. Let $\mathcal{E}_i(P^\pi_{1:N})$ denote the measure of Markov entanglement of
--   agent $i$ with respect to the $\mu^\pi_{1:N}$-weighted agent-wise total variation distance.
--   Then the decomposition error, measured in the $\mu^\pi_{1:N}$-norm, satisfies
--
--   $$\Bigl\| \, Q^\pi_{1:N}(s,a) - \sum_{i=1}^{N} Q^\pi_i(s_i,a_i) \, \Bigr\|_{\mu^\pi_{1:N}}
--   \;\le\; \frac{4\gamma \sum_{i=1}^{N} \mathcal{E}_i\bigl(P^\pi_{1:N}\bigr)\, r^i_{\max}}{(1-\gamma)^2}.$$
--
--   ## Notes
--
--   This is the paper's central quantitative result and the goal of this mission. It says the
--   error incurred by approximating a global value function by a sum of local ones is
--   controlled, in the occupancy-weighted norm, by how **entangled** the joint transition
--   matrix is — with no structural assumption on the MDP beyond bounded rewards and a
--   stationary occupancy measure.
--
--   The shape of the bound is worth reading. The error is *linear* in the entanglement
--   measures $\mathcal{E}_i$, so a weakly entangled system has a small decomposition error and a
--   separable one has none at all, recovering the exact decomposition. The factor
--   $(1-\gamma)^{-2}$ is the usual quadratic blow-up from propagating a one-step transition
--   perturbation through a discounted value function, and the $r^i_{\max}$ weights say each
--   agent contributes in proportion to its own reward scale.
--
--   The $\mu$-weighted norm matters: it averages the error over the states the policy actually
--   visits rather than taking a worst case, which is what makes the bound useful in large
--   systems where rare states would otherwise dominate. This is what lets the paper conclude,
--   in its restless-bandit application, that index policies incur only $O(\sqrt{N})$
--   decomposition error across $N$ agents.
--
--   Relevant search terms: value decomposition error bound, multi-agent reinforcement learning
--   theory, Markov entanglement, separability of transition kernels, weakly coupled MDPs,
--   occupancy-weighted norm, discounted value function perturbation.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Theorem 6, p. 21

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem multi_agent_decomposition_error
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |r i s| ≤ rmax i)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q)
    -- each `Pl i` attains agent `i`'s measure of entanglement, and `Qi i` is the
    -- value function of that local chain: this is what ties `Qi` to the data.
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hopt : ∀ i, muAgentTVDistN i μ P (Pl i) = entanglementN i μ P)
    (hQi : ∀ i, IsBellmanQ (Pl i) (r i) γ (Qi i)) :
    muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
      ≤ 4 * γ * (∑ i, entanglementN i μ P * rmax i) / (1 - γ) ^ 2 := by
  sorry

end MarkovEntanglement
