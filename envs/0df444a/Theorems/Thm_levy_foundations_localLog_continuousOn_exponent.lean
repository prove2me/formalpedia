-- Prove2me | Theorems.Thm_levy_foundations_localLog_continuousOn_exponent
-- name    : levy_foundations_localLog_continuousOn_exponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:47:05.008153+00:00
-- url     : https://prove2.me/theorems/230cfb80-4d18-46aa-8b73-7dcc68f61753
-- title:
--   The local logarithmic exponent is continuous on its good domain
-- statement:
--   The local logarithmic exponent is continuous on its good domain.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L96

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent

open Filter Topology

theorem levy_foundations_localLog_continuousOn_exponent
    {E : Type*} [TopologicalSpace E] [Zero E]
    {φ : E → ℂ} (hφ_cont : Continuous φ) :
    ContinuousOn (LevyFoundations.LocalLog.localCharExponent φ)
      (LevyFoundations.LocalLog.goodDomain φ) := by sorry
