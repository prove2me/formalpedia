-- Prove2me | Theorems.Thm_bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
-- name    : bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T07:24:37.579549+00:00
-- url     : https://prove2.me/theorems/ea982007-a5c9-4d4d-a17f-f8a621e2fb0e
-- statement:
--   This is the corrected three-sample Bernoulli product lower bound used in the all-distinct decoupling estimates for the Candes-Recht Neumann-series certificate. Work in the Bernoulli observation model on subsets of $[n_1]	imes[n_2]$, sampled independently with probability $p$, with $0le ple 1$.
--
--   Let $E_{\mathrm{pair}}(\Omega_2,\Omega_3)$ be a good event for the second and third independent samples. Let $E_{\mathrm{triple}}(\Omega_1,\Omega_2,\Omega_3)$ be the desired three-sample good event. Assume
--
--   $$
--   \mathbb P_p^{\otimes 2}(E_{\mathrm{pair}})\ge 1-c_{\mathrm{pair}}s,
--   $$
--
--   and, whenever $E_{\mathrm{pair}}(\Omega_2,\Omega_3)$ holds,
--
--   $$
--   \mathbb P_p\{\Omega_1:E_{\mathrm{triple}}(\Omega_1,\Omega_2,\Omega_3)\}ge 1-c_{\mathrm{cond}}s.
--   $$
--
--   The added hypothesis $0le c_{\mathrm{cond}}s$ is essential; without it the conditional statement can be vacuous on an empty pair event. Under the corrected hypotheses,
--
--   $$
--   \mathbb P_p^{\otimes 3}(E_{\mathrm{triple}})\ge 1-(c_{\mathrm{cond}}+c_{\mathrm{pair}})s.
--   $$
--
--   In applications $s=n^{-\beta}$ and $c_{\mathrm{cond}}>0$, so the new sign condition is automatic.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem bernoulli_triple_event_probability_from_pair_marginal_and_conditional_lower_bounds_of_nonneg
    {n₁ n₂ : ℕ} (p cPair cCond scale : ℝ)
    (EventPair :
      Finset (Fin n₁ × Fin n₂) → Finset (Fin n₁ × Fin n₂) → Prop)
    (EventTriple :
      Finset (Fin n₁ × Fin n₂) →
      Finset (Fin n₁ × Fin n₂) →
      Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    0 ≤ cCond * scale →
    bernoulliPairEventProb p EventPair ≥ 1 - cPair * scale →
    (∀ Omega2 Omega3,
      EventPair Omega2 Omega3 →
        bernoulliEventProb p (fun Omega1 => EventTriple Omega1 Omega2 Omega3) ≥
          1 - cCond * scale) →
    bernoulliTripleEventProb p EventTriple ≥ 1 - (cCond + cPair) * scale := by
  sorry
