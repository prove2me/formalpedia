-- Prove2me | Theorems.Thm_MarkovEntanglement_local_transition_deviation_mu_le_two_entanglement
-- name    : MarkovEntanglement.local_transition_deviation_mu_le_two_entanglement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-07T16:13:52.137007+00:00
-- url     : https://prove2.me/theorems/21784cd6-6c24-41d6-b111-2e1e68e39e32
-- title:
--   Local transition deviates in $\mu_i$-norm by at most twice the $\mu$-weighted measure of entanglement
-- statement:
--   **Theorem 5, first part (Chen and Peng, p. 19), $N$-agent form — the $\mu$-weighted row of Table 1.**
--
--   Consider an $N$-agent MDP with joint transition $P^\pi_{1:N}$ and occupancy measure $\mu$ strictly positive and stationary. Fix an agent $i$, let $P^\pi_i$ be the local (marginalized) transition induced by $P^\pi_{1:N}$ and $\mu$ via Eq. (2), and let $P_i$ attain the measure of Markov entanglement of agent $i$ with respect to the **$\mu$-weighted** agent-wise total variation distance.
--
--   Then the local transition deviates from that optimal independent approximation by at most twice the entanglement, measured in the $\mu_i$-weighted norm:
--   $$\big\|P^\pi_i - P_i\big\|_{\mu_i} \le 2\,\mathcal{E}_i\big(P^\pi_{1:N}\big),$$
--   where $\mu_i$ is agent $i$'s local stationary distribution. By Lemma 5 that distribution is exactly the marginal of the global occupancy measure onto agent $i$'s coordinate, which is how it is written here.
--
--   This is the $\mu$-weighted counterpart of the first part of Theorem 8, and the weighting on both sides is what makes it true: the same statement with a uniform conclusion fails, because a rarely visited local state contributes almost nothing to the $\mu$-average defining the entanglement while its conditional deviation can remain of constant order. Weighting the conclusion by the same marginal exactly compensates. In fact the sharp form of the argument gives the bound with constant $1$ rather than $2$, and is tight; the factor $2$ stated here is the source's.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Theorem 5, p. 19 (first part), N-agent form; local stationary distribution identified via Lemma 5, pp. 38-39

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem local_transition_deviation_mu_le_two_entanglement
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (μ : Joint S → ℝ) (hμ : IsPositiveDist μ) (hstat : IsStationary P μ) (i : Fin N)
    (Pi Ptrue : Matrix (S i) (S i) ℝ)
    (hPi : IsTransitionMatrix Pi)
    (hopt : muAgentTVDistN i μ P Pi = entanglementN i μ P)
    (hPtrue : IsTransitionMatrix Ptrue) (htrue : IsLocalTransitionN i P μ Ptrue) :
    muTVDist (marginalDist i μ) Ptrue Pi ≤ 2 * entanglementN i μ P := by
  sorry

end MarkovEntanglement
