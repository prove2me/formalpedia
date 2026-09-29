-- Prove2me | Theorems.Thm_MarkovEntanglement_local_transition_deviation_le_two_atv_entanglement
-- name    : MarkovEntanglement.local_transition_deviation_le_two_atv_entanglement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-07T16:12:46.102465+00:00
-- url     : https://prove2.me/theorems/788e3389-134a-4e59-8b0e-8789ab642e52
-- title:
--   Local transition deviates by at most twice the ATV measure of entanglement
-- statement:
--   **Theorem 8, first part (Chen and Peng, p. 40), $N$-agent form on the supremum row of Table 1.**
--
--   Consider an $N$-agent MDP with joint transition $P^\pi_{1:N}$ and a policy $\pi$, with occupancy measure $\mu$ strictly positive and stationary. Fix an agent $i$, let $P^\pi_i$ be the local (marginalized) transition induced by $P^\pi_{1:N}$ and $\mu$ via Eq. (2), and let $P_i$ attain the measure of Markov entanglement of agent $i$ **with respect to the unweighted agent-wise total variation distance**.
--
--   Then the local transition deviates from that optimal independent approximation by at most twice the entanglement, uniformly over local state-action pairs:
--   $$\big\|P^\pi_i - P_i\big\|_\infty \le 2\,\mathcal{E}_i\big(P^\pi_{1:N}\big).$$
--
--   The measure here is the supremum-based one, $\mathcal{E}_i = \inf_{P_i} \sup_{s,a} \tfrac12\sum_t |P_i^{\text{marg}}(t\mid s,a) - P_i(t\mid s_i,a_i)|$. This pairing matters: Table 1 (p. 20) matches the unweighted distances with $\|\cdot\|_\infty$ and the $\mu$-weighted ones with $\|\cdot\|_\mu$, and the uniform conclusion is *false* if the entanglement is measured in the $\mu$-weighted distance, since a rarely visited local state can contribute almost nothing to a $\mu$-average while its conditional deviation stays of constant order.
--
--   Strict positivity of $\mu$ forces the joint space to be nonempty, hence every local state-action pair has positive marginal — which is what licenses passing from the conditional average defining $P^\pi_i$ to a uniform bound.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Theorem 8, p. 40 (first part), with the distance/norm pairing of Table 1, p. 20

import Mathlib
import Definitions.Def_markov_entanglement_multi_atv

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem local_transition_deviation_le_two_atv_entanglement
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (μ : Joint S → ℝ) (hμ : IsPositiveDist μ) (hstat : IsStationary P μ) (i : Fin N)
    (Pi Ptrue : Matrix (S i) (S i) ℝ)
    (hPi : IsTransitionMatrix Pi)
    (hopt : agentTVDistN i P Pi = agentEntanglementWith i (agentTVDistN i) P)
    (hPtrue : IsTransitionMatrix Ptrue) (htrue : IsLocalTransitionN i P μ Ptrue) :
    ∀ s t, |Ptrue s t - Pi s t| ≤ 2 * agentEntanglementWith i (agentTVDistN i) P := by
  sorry

end MarkovEntanglement
