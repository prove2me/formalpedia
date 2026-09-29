-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_high_probability_regret_known_reward_diam_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T19:44:13.525287+00:00
-- url     : https://prove2.me/submissions/04211134-6e03-4480-9e80-e919535162bd

import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_good_event_regret_bound

open MeasureTheory ProbabilityTheory ENNReal BanditAlgorithm

/-!
Theorem 38.6 from its high-probability-event form.

The child supplies, for each MDP, an event `G` carrying two pieces of data: its
complement has probability at most `δ`, and on it the regret is strictly below
the target bound.  All that is left is to observe that the bad event of the
statement is contained in `Gᶜ` — a trajectory on which the bound is at most the
regret cannot lie in `G`, where the regret is strictly below the bound — and to
apply monotonicity of the measure.
-/

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, 0 < S → 0 < A → 0 < n →
        ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 →
          ∀ r : Fin S → Fin A → ℝ, (∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) →
            ∃ π : MDPPolicy S A,
              ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating →
                1 ≤ mdpDiameter M →
                ∀ μ0 : MDPStateDistribution S,
                  mdpMeasure M μ0 π n
                      {h | C * mdpDiameter M * S *
                          Real.sqrt (A * n * Real.log (n * S * A / δ)) ≤
                        mdpRegret M n h} ≤
                    ENNReal.ofReal δ := by
  obtain ⟨C, hC, hmain⟩ := BanditAlgorithm.mdp_ucrl2_good_event_regret_bound
  refine ⟨C, hC, ?_⟩
  intro S A n hS hA hn δ hδ r hr
  obtain ⟨π, hπ⟩ := hmain S A n hS hA hn δ hδ r hr
  refine ⟨π, ?_⟩
  intro M hMr hMcomm hMD μ0
  obtain ⟨G, hGprob, hGbound⟩ := hπ M hMr hMcomm hMD μ0
  refine le_trans (measure_mono ?_) hGprob
  intro h hh
  exact fun hG ↦ absurd (hGbound h hG) (not_lt.mpr hh)
