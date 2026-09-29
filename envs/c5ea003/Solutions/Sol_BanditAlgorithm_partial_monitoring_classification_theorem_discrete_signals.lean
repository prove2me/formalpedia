-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_classification_theorem_discrete_signals
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T15:37:30.040142+00:00
-- url     : https://prove2.me/submissions/65914623-2717-421a-b485-c4968e67ab19

import Theorems.Thm_BanditAlgorithm_partial_monitoring_trivial_zero_regret
import Theorems.Thm_BanditAlgorithm_partial_monitoring_easy_sqrt_lower_bound
import Theorems.Thm_BanditAlgorithm_partial_monitoring_easy_sqrt_upper_bound_discrete_signals
import Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_game_lower_bound
import Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_rpow_two_thirds_upper_bound_discrete_signals
import Theorems.Thm_BanditAlgorithm_partial_monitoring_hopeless_linear_lower_bound

open MeasureTheory ProbabilityTheory

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊) :
    (¬ BanditAlgorithm.HasNeighbouringActions G →
      ∀ n : ℕ, BanditAlgorithm.pmMinimaxRegret G n = 0) ∧
    (BanditAlgorithm.LocallyObservable G ∧ BanditAlgorithm.HasNeighbouringActions G →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        c * Real.sqrt n ≤ BanditAlgorithm.pmMinimaxRegret G n ∧
        BanditAlgorithm.pmMinimaxRegret G n ≤ C * Real.sqrt n) ∧
    (BanditAlgorithm.GloballyObservable G ∧ ¬ BanditAlgorithm.LocallyObservable G →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ BanditAlgorithm.pmMinimaxRegret G n ∧
        BanditAlgorithm.pmMinimaxRegret G n ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3)) ∧
    (BanditAlgorithm.HasNeighbouringActions G ∧ ¬ BanditAlgorithm.GloballyObservable G →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        c * (n : ℝ) ≤ BanditAlgorithm.pmMinimaxRegret G n) := by
  constructor
  · exact BanditAlgorithm.partial_monitoring_trivial_zero_regret G
  constructor
  · intro h
    obtain ⟨c, hc, Nc, hlower⟩ :=
      BanditAlgorithm.partial_monitoring_easy_sqrt_lower_bound G h
    obtain ⟨C, hC, NC, hupper⟩ :=
      BanditAlgorithm.partial_monitoring_easy_sqrt_upper_bound_discrete_signals G h
    refine ⟨c, C, hc, hC, max Nc NC, ?_⟩
    intro n hn
    exact ⟨hlower n ((Nat.le_max_left _ _).trans hn),
      hupper n ((Nat.le_max_right _ _).trans hn)⟩
  constructor
  · intro h
    obtain ⟨c, hc, hlower⟩ :=
      BanditAlgorithm.partial_monitoring_hard_game_lower_bound G h.1 h.2
    obtain ⟨C, hC, N, hupper⟩ :=
      BanditAlgorithm.partial_monitoring_hard_rpow_two_thirds_upper_bound_discrete_signals G h
    exact ⟨c, C, hc, hC, N, fun n hn => ⟨hlower n, hupper n hn⟩⟩
  · exact BanditAlgorithm.partial_monitoring_hopeless_linear_lower_bound G
