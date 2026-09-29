-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_trivial_zero_regret
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T16:19:55.569089+00:00
-- url     : https://prove2.me/submissions/6568ed80-5bcd-462c-9ed3-a64650bd2e4e

import Theorems.Thm_BanditAlgorithm_pmMinimaxRegret_eq_zero_of_universally_optimal
import Theorems.Thm_BanditAlgorithm_partial_monitoring_no_neighbours_has_universally_optimal_action

open MeasureTheory ProbabilityTheory

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (h : ¬ BanditAlgorithm.HasNeighbouringActions G) :
    ∀ n : ℕ, BanditAlgorithm.pmMinimaxRegret G n = 0 := by
  intro n
  cases k with
  | zero =>
      letI : IsEmpty (BanditAlgorithm.PMPolicy 0 𝕊) := ⟨fun π ↦ by
        have hmarkov : IsMarkovKernel (π.select 0) := π.markov 0
        have hzero : π.select 0 = 0 := Kernel.eq_zero_of_isEmpty_right _
        rw [hzero] at hmarkov
        exact ProbabilityTheory.Kernel.not_isMarkovKernel_zero hmarkov⟩
      unfold BanditAlgorithm.pmMinimaxRegret
      change sInf (Set.range (fun π : BanditAlgorithm.PMPolicy 0 𝕊 =>
        ⨆ i : Fin n → Fin d, BanditAlgorithm.pmRegret G π n i)) = 0
      rw [Set.range_eq_empty_iff.mpr (inferInstance : IsEmpty (BanditAlgorithm.PMPolicy 0 𝕊)),
        Real.sInf_empty]
  | succ k =>
      cases d with
      | zero =>
          cases n with
          | zero => simp [BanditAlgorithm.pmMinimaxRegret, BanditAlgorithm.pmRegret]
          | succ n => simp [BanditAlgorithm.pmMinimaxRegret]
      | succ d =>
          obtain ⟨a, ha⟩ :=
            BanditAlgorithm.partial_monitoring_no_neighbours_has_universally_optimal_action
              G (Nat.zero_lt_succ k) (Nat.zero_lt_succ d) h
          exact BanditAlgorithm.pmMinimaxRegret_eq_zero_of_universally_optimal G a ha n
