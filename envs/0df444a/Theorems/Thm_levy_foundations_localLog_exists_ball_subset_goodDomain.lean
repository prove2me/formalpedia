-- Prove2me | Theorems.Thm_levy_foundations_localLog_exists_ball_subset_goodDomain
-- name    : levy_foundations_localLog_exists_ball_subset_goodDomain
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T20:47:32.368395+00:00
-- url     : https://prove2.me/theorems/f74e39dc-42eb-49f1-b4e5-7f2992916982
-- title:
--   A neighbourhood of zero admits a continuous complex logarithm
-- statement:
--   A neighbourhood of zero admits a continuous complex logarithm.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L107

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent

open Filter Topology

theorem levy_foundations_localLog_exists_ball_subset_goodDomain
    {E : Type*} [SeminormedAddCommGroup E]
    {φ : E → ℂ} (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : E) ε ⊆
      LevyFoundations.LocalLog.goodDomain φ := by sorry
