-- Prove2me | Theorems.Thm_MarkovEntanglement_local_stationary_eq_marginal
-- name    : MarkovEntanglement.local_stationary_eq_marginal
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T05:24:47.825727+00:00
-- url     : https://prove2.me/theorems/196ab9e8-7392-470a-800c-5d5ac4b46450
-- title:
--   The local stationary distribution is the marginal of the global one
-- statement:
--   ## Statement
--
--   **Lemma.** Let $\mu^\pi$ be a stationary distribution of the joint transition $P^\pi$,
--   and let $P^\pi_i$ be agent $i$'s marginalised local transition. Then $P^\pi_i$ has stationary
--   distribution
--   $$\mu^\pi_i(s_i,a_i) \;=\; \sum_{s_{-i},\,a_{-i}} \mu^\pi(s,a),$$
--   the marginal of the global occupancy measure onto agent $i$'s coordinates.
--
--   ## Notes
--
--   A compatibility result that makes the occupancy-weighted norms meaningful. The global
--   analysis weights states by $\mu^\pi$; the per-agent analysis weights them by $\mu^\pi_i$.
--   This lemma says the two agree — the local weighting is exactly the marginal of the global
--   one, so no discrepancy is introduced when a global bound is projected onto one agent.
--
--   Without it, the per-agent bounds and the global bound would be measured against different
--   reference distributions and could not be combined.
--
--   Search terms: marginal of stationary distribution, occupancy measure of a marginalised
--   Markov chain, projected transition matrix, lumping of Markov chains.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Lemma 5, pp. 38-39

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem local_stationary_eq_marginal
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (μ : Joint S → ℝ) (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (i : Fin N) (Pi : Matrix (S i) (S i) ℝ)
    (hPi : IsLocalTransitionN i P μ Pi) :
    IsStationary Pi (marginalDist i μ) := by
  sorry

end MarkovEntanglement
