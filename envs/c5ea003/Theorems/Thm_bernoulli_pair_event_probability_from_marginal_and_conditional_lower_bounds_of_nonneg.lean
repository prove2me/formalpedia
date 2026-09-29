-- Prove2me | Theorems.Thm_bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
-- name    : bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T07:06:13.210477+00:00
-- url     : https://prove2.me/theorems/6ebeb434-3a19-4556-b590-b3b95eb69064
-- statement:
--   This is the corrected two-sample Bernoulli product lower bound used in the matrix-completion decoupling estimates. Work in the Bernoulli observation model on subsets of the matrix-entry set $[n_1]	imes[n_2]$, where each entry is sampled independently with probability $p$ and $0le ple 1$.
--
--   Let $E_{\mathrm{marg}}(\Omega_2)$ be a marginal good event for the second sample, and let $E_{\mathrm{pair}}(\Omega_1,\Omega_2)$ be the desired two-sample good event. Assume
--
--   $$
--   \mathbb P_p(E_{\mathrm{marg}})\ge 1-c_{\mathrm{marg}}s,
--   $$
--
--   and, for every $\Omega_2$ satisfying $E_{\mathrm{marg}}(\Omega_2)$,
--
--   $$
--   \mathbb P_p\{\Omega_1: E_{\mathrm{pair}}(\Omega_1,\Omega_2)\}ge 1-c_{\mathrm{cond}}s.
--   $$
--
--   The additional hypothesis $0le c_{\mathrm{cond}}s$ is essential: without it the conditional lower bound can be vacuous when the marginal event is empty, which was the flaw in the deprecated predecessor node. Under these assumptions the product two-sample event satisfies
--
--   $$
--   \mathbb P_p^{\otimes 2}(E_{\mathrm{pair}})\ge 1-(c_{\mathrm{cond}}+c_{\mathrm{marg}})s.
--   $$
--
--   In the Candes-Recht decomposition this lemma is the reusable probability bookkeeping step for two-copy decoupling arguments. In applications, $s=n^{-\beta}$, so the new nonnegativity side condition follows from positivity of $c_{\mathrm{cond}}$ and of $n^{-\beta}$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
    {n₁ n₂ : ℕ} (p cMarg cCond scale : ℝ)
    (EventMarg : Finset (Fin n₁ × Fin n₂) → Prop)
    (EventPair :
      Finset (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    0 ≤ cCond * scale →
    bernoulliEventProb p EventMarg ≥ 1 - cMarg * scale →
    (∀ Omega2,
      EventMarg Omega2 →
        bernoulliEventProb p (fun Omega1 => EventPair Omega1 Omega2) ≥
          1 - cCond * scale) →
    bernoulliPairEventProb p EventPair ≥ 1 - (cCond + cMarg) * scale := by
  sorry
