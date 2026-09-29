-- Prove2me | Theorems.Thm_MarkovEntanglement_weakly_coupled_entanglement_le_policy_mismatch
-- name    : MarkovEntanglement.weakly_coupled_entanglement_le_policy_mismatch
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-10T13:55:43.377279+00:00
-- url     : https://prove2.me/theorems/92d634aa-0410-406d-9bc7-abc8541a0f1f
-- title:
--   Weakly-coupled MDPs: entanglement is bounded by policy mismatch
-- statement:
--   ## Statement
--
--   Consider an $N$-agent **weakly-coupled** MDP: each agent's next state depends only on its own state and action, so the joint kernel factorises as
--   $$P(s' \mid s, a) \;=\; \prod_{i=1}^{N} P_i\bigl(s'_i \mid s_i, a_i\bigr),$$
--   while the agents remain coupled through the joint policy $\pi : S \to \Delta(A)$ (and, in applications, through constraints on the joint action). Let $\mu^\pi_{1:N}$ be an occupancy measure on joint state-action pairs, stationary for the induced transition $P^\pi$.
--
--   Then for every agent $i$ and **every local policy** $\pi'$ that reads only agent $i$'s own state, the measure of Markov entanglement with respect to the $\mu$-weighted agent-wise total variation distance is bounded by the policy mismatch:
--   $$\mathcal{E}_i\bigl(P^\pi_{1:N}\bigr) \;\le\; \frac{1}{2}\sum_{s} \mu^\pi_{1:N}(s) \sum_{a_i} \Bigl| \pi(a_i \mid s) - \pi'(a_i \mid s_i) \Bigr| .$$
--   Since this holds for every $\pi'$, it holds for the minimising one.
--
--   ## Notes
--
--   The transition term has vanished. In a general multi-agent MDP the measure of entanglement has to account for both how the *transition* couples the agents and how the *policy* does; under weak coupling the transition contributes nothing, and all the entanglement is in the policy. That is what makes this bound the gateway to the restless-bandit theory: it reduces "how entangled is this system?" to "how far is this joint policy from acting on each agent independently?", a question about $\pi$ alone.
--
--   **Why the local kernels drop out.** The candidate local transition is the obvious one — move with agent $i$'s own kernel, then act with $\pi'$ — and its error against the true marginal is
--   $$\sum_{s'_{-i}} P(s' \mid s,a)\Bigl(\pi(a'_i \mid s') - \pi'(a'_i \mid s'_i)\Bigr).$$
--   Summing a product kernel over every coordinate but one leaves that coordinate's kernel, because the other rows sum to one; so the difference of transitions collapses into a difference of *policies*, weighted by where the system goes next. Averaging that against the occupancy measure and using stationarity turns the weight into the occupancy measure itself, which is the displayed bound.
--
--   **Scope.** As the source observes, the linear coupling constraint $\sum_i d_i(s_i,a_i) \le b$ of Definition 11 is never used: the bound holds for multi-agent MDPs with *arbitrary* coupling, provided only that the agents follow local transition kernels. Nothing here needs a discount factor, a reward, or a budget.
--
--   Search terms: weakly-coupled MDP, Markov entanglement bound, policy mismatch, local policy approximation, product transition kernel, restless multi-armed bandit, value decomposition.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Proposition 1, p. 22 (proof p. 23)

import Mathlib
import Definitions.Def_markov_entanglement_policy

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem weakly_coupled_entanglement_le_policy_mismatch
    {N : ℕ} {St Act : Fin N → Type*}
    [∀ i, Fintype (St i)] [∀ i, DecidableEq (St i)]
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    (P : JointState St → JointAction Act → JointState St → ℝ)
    (Pl : ∀ i, St i → Act i → St i → ℝ)
    (hPl : IsLocalKernel Pl) (hwc : IsWeaklyCoupled P Pl)
    (π : JointState St → JointAction Act → ℝ) (hπ : IsJointPolicy π)
    (μ : Joint (StateAction St Act) → ℝ) (hμ : IsPositiveDist μ)
    (hstat : IsStationary (inducedTransition P π) μ)
    (i : Fin N) (πl : St i → Act i → ℝ) (hπl : IsLocalPolicy πl) :
    entanglementN i μ (inducedTransition P π) ≤ policyMismatch i π μ πl := by
  sorry

end MarkovEntanglement
