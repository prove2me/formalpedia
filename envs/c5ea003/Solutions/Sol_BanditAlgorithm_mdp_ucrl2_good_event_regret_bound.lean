-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_good_event_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T19:57:52.492827+00:00
-- url     : https://prove2.me/submissions/fedc2943-ac74-40b6-82b9-47b5f4756dc1

import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_regret_bound_of_optimistic_phase_run
import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_optimistic_phase_run_on_good_event

open MeasureTheory ProbabilityTheory ENNReal BanditAlgorithm

/-!
Theorem 38.6 on the confidence good event, split into its probabilistic and its
deterministic half.

The interface between the two is an *optimistic phase run*: a partition of the
`n` rounds into phases, together with, for each phase, a gain, a bias function
and a transition matrix which solve the Bellman equation along the realised
trajectory, are optimistic, have span at most the diameter, and whose
accumulated estimation error and martingale fluctuation obey explicit bounds.

The probabilistic child produces such a run on an event of probability at least
`1 - δ`; the deterministic child turns any such run into the regret bound.  The
reduction is the composition, together with the observation that the hypothesis
`1 ≤ D(M)` forces at least two states: for a single state no pair `src ≠ tgt`
exists, the supremum defining the diameter is empty, and `D(M) = 0`.
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
                  ∃ G : Set (MDPTrajectory S A n),
                    mdpMeasure M μ0 π n Gᶜ ≤ ENNReal.ofReal δ ∧
                    ∀ h ∈ G, mdpRegret M n h <
                      C * mdpDiameter M * S *
                        Real.sqrt (A * n * Real.log (n * S * A / δ)) := by
  obtain ⟨C, hC, hdet⟩ :=
    BanditAlgorithm.mdp_ucrl2_regret_bound_of_optimistic_phase_run
  refine ⟨C, hC, ?_⟩
  intro S A n hS hA hn δ hδ r hr
  by_cases hS2 : 2 ≤ S
  · obtain ⟨π, hrun⟩ :=
      BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_on_good_event
        S A n hS2 hA hn δ hδ r hr
    refine ⟨π, ?_⟩
    intro M hMr hMcomm hMD μ0
    obtain ⟨G, hGprob, hGcert⟩ := hrun M hMr hMcomm hMD μ0
    refine ⟨G, hGprob, ?_⟩
    intro h hh
    obtain ⟨st, act, K, τ, ρ, v, q, hsa, hτ0, hτK, hτm, hK, hopt, hspan,
      hbell, hest, hmart⟩ := hGcert h hh
    exact hdet S A n hS2 hA hn δ hδ M hMD h st act hsa K τ ρ v q
      hτ0 hτK hτm hK hopt hspan hbell hest hmart
  · -- A single state: no ordered pair of distinct states, so `D(M) = 0`.
    refine ⟨mdpMemorylessDetPolicy (fun _ ↦ ⟨0, hA⟩), ?_⟩
    intro M hMr hMcomm hMD μ0
    exfalso
    have hS1 : S = 1 := by omega
    subst hS1
    have hzero : mdpDiameterENN M = 0 := by
      refine le_antisymm ?_ (by simp)
      simp only [mdpDiameterENN]
      refine iSup_le fun src ↦ iSup_le fun tgt ↦ iSup_le fun hne ↦ ?_
      exact absurd (Subsingleton.elim src tgt) hne
    rw [show mdpDiameter M = (mdpDiameterENN M).toReal from rfl, hzero] at hMD
    simp only [ENNReal.toReal_zero] at hMD
    linarith
