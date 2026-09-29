-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_expected_regret_known_reward_diam_ge_one
-- name    : BanditAlgorithm.mdp_ucrl2_expected_regret_known_reward_diam_ge_one
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:59:54.457956+00:00
-- url     : https://prove2.me/theorems/67cf5d56-4430-49eb-b1c1-f57734deec9e
-- title:
--   UCRL2 expected regret bound with known rewards
-- statement:
--   There is a universal constant $C>0$ such that, for every positive number of states $S$, actions $A$, and rounds $n$, and every known reward function $r:\mathcal S\times\mathcal A\to[0,1]$, some policy independent of the unknown transition matrix satisfies, for every communicating MDP $M$ with reward function $r$, diameter $D(M)\ge1$, and every initial distribution,
--
--   $$
--   \mathbb E[\widehat R_n]
--   \le
--   1+C D(M)S\sqrt{2A n\log n}.
--   $$
--
--   This is the expected-regret form of UCRL2 obtained from the high-probability analysis with a horizon-dependent confidence level. It uses the same known-reward learning model as Theorem 38.6 and excludes only the zero-diameter degeneracy.
--
--   **Formalization Note** The policy may depend on the horizon and the known reward function, matching the quantifier order in the source analysis.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Eq. (38.12), printed p. 523 / PDF p. 532, derived from Theorem 38.6 in Exercise 38.18.

import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.mdp_ucrl2_expected_regret_known_reward_diam_ge_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, 0 < S → 0 < A → 0 < n →
        ∀ r : Fin S → Fin A → ℝ, (∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) →
          ∃ π : MDPPolicy S A,
            ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating →
              1 ≤ mdpDiameter M →
              ∀ μ0 : MDPStateDistribution S,
                ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) ≤
                  1 + C * mdpDiameter M * S *
                    Real.sqrt (2 * A * n * Real.log n) := by
  sorry
