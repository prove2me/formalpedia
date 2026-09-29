-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_hard_game_tradeoff
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:48:40.296919+00:00
-- url     : https://prove2.me/submissions/5fedb31a-5c5c-4a76-b435-9df07766b041

import Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_geometric_alternatives
import Theorems.Thm_BanditAlgorithm_partial_monitoring_tradeoff_of_geometric_alternatives

open MeasureTheory ProbabilityTheory

theorem solution {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (hglob : BanditAlgorithm.GloballyObservable G)
    (hloc : ¬ BanditAlgorithm.LocallyObservable G) :
    ∃ ε C δ : ℝ, 0 < ε ∧ 0 ≤ C ∧ 0 < δ ∧
      ∀ (n : ℕ), 1 ≤ n → ∃ x : ℝ, 0 ≤ x ∧
        ε / 2 * x +
            (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
              Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) ≤
          2 * BanditAlgorithm.pmMinimaxRegret G n := by
  letI : DecidableEq 𝕊 := Classical.decEq 𝕊
  apply BanditAlgorithm.partial_monitoring_tradeoff_of_geometric_alternatives G
  exact BanditAlgorithm.partial_monitoring_hard_geometric_alternatives G hglob hloc
