-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_game_lower_bound
-- name    : BanditAlgorithm.partial_monitoring_hard_game_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-30T20:12:48.634209+00:00
-- url     : https://prove2.me/theorems/0a4822ef-6683-4dc7-b30c-26a614d06666
-- statement:
--   (Hard games, Theorem 37.12) If $G$ is globally observable but not locally observable, then there exists a game-dependent constant $c_G > 0$ such that for every horizon $n$,
--
--   $$R_n^*(G) \ge c_G\, n^{2/3}.$$
-- source:
--   L&S Theorem 37.12, p.488

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.SpecialFunctions.Pow.Real


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_hard_game_lower_bound {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] (G : PartialMonitoringGame k d 𝕊)
    (hglob : GloballyObservable G) (hloc : ¬ LocallyObservable G) :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ pmMinimaxRegret G n := by
  sorry
