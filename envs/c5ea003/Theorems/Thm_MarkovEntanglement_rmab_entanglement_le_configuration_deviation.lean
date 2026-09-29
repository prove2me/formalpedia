-- Prove2me | Theorems.Thm_MarkovEntanglement_rmab_entanglement_le_configuration_deviation
-- name    : MarkovEntanglement.rmab_entanglement_le_configuration_deviation
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-28T02:22:58.736284+00:00
-- url     : https://prove2.me/theorems/6de07272-571d-4c20-a2bc-7f8d56743132
-- title:
--   Entanglement is bounded by the configuration's deviation (Lem. 2 / 8)
-- statement:
--   Consider an $N$-agent restless multi-armed bandit under an index policy $\pi$ with injective priority index $\nu$ and budget $\lfloor \alpha N \rfloor$, and let $\mu^\pi_{1:N}$ be a stationary occupancy distribution of the induced chain. Let $m^\ast$ be a configuration (a point of the simplex) — in the application, the mean-field fixed point.
--
--   Then for every agent $i$ the measure of Markov entanglement of the joint chain, with respect to the occupancy-weighted agent-wise total variation distance, is bounded by the expected deviation of the system configuration from $m^\ast$:
--
--   $$\mathcal{E}_i(P^\pi_{1:N}) \;\le\; |S|^2 \cdot \mathbb{E}\big[\|m - m^\ast\|_\infty\big],$$
--
--   the expectation taken over the stationary occupancy measure.
--
--   This is where Proposition 1 is cashed in. Proposition 1 bounds the entanglement of a weakly-coupled system by the occupancy-weighted distance between the realised policy's per-agent marginal and any local policy; here the local policy chosen as witness is the mean-field limiting policy at $m^\ast$, which activates an agent in state $x$ with the probability the index policy would allot at the configuration $m^\ast$. Homogeneity of the agents makes the mismatch the same for every agent, so the supremum over $i$ may be replaced by an average, and the average collapses into a sum over local states weighted by the configuration. The remaining per-state estimate compares the fraction the index policy actually activates in state $x$ with the fraction it would activate at $m^\ast$; both are ratios of a budget residual to a state occupancy, and both numerator and denominator move by at most $|S| \cdot \|m - m^\ast\|_\infty$, which gives the stated bound.
--
--   With this lemma the asymptotic analysis reduces entirely to a question about the configuration process: how far does $m$ stray from the mean-field fixed point under the stationary distribution?
--
--   The stationary distribution is assumed **exchangeable** — invariant under permuting the agents. The source's proof exchanges agent indices and asserts the stationary distribution is unchanged, which is exactly exchangeability; it holds automatically for the unique stationary distribution of an ergodic symmetric chain, but a reducible chain also has non-exchangeable stationary distributions concentrated on asymmetric closed classes, for which the agent-averaging step (and with it the stated bound) is not available. The hypothesis records precisely the consequence of ergodicity the argument uses.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Section 7.1.2 p. 25 (Lemma 2) and Appendix I p. 42 (Lemma 8)

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Lemma 2 / Lemma 8.  For an index policy, the measure of Markov entanglement of any agent,
with respect to the occupancy-weighted agent-wise total variation distance, is bounded by the
expected deviation of the system configuration from the mean-field fixed point:

`Eᵢ(P^π_{1:N}) ≤ |S|² · E[‖m − m✦‖_∞]`,

the expectation taken over the stationary occupancy measure.  This is where Proposition 1 is
cashed in: the local policy witnessing the bound is the mean-field limiting policy at `m✦`. -/
theorem rmab_entanglement_le_configuration_deviation
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (N : ℕ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π)
    (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
    (hμ : IsDist μ) (hexch : IsExchangeableDist μ)
    (hstat : IsStationary (inducedTransition
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ)
    (i : Fin N) :
    entanglementN i μ (inducedTransition
        (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
      ≤ (Fintype.card S : ℝ) ^ 2 *
          ∑ p : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)),
            μ p * supNorm (fun x => configuration (fun j => (p j).1) x - mstar x) := by
  sorry

/-! ### M4 — Lemma 9, one-step concentration (Gast, Gaujal and Yan) -/

end MarkovEntanglement
