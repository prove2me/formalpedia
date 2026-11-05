-- Prove2me | Theorems.Thm_levy_foundations_localLog_isOpen_goodDomain
-- name    : levy_foundations_localLog_isOpen_goodDomain
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:46:50.189356+00:00
-- url     : https://prove2.me/theorems/4a26be60-ebff-45e2-b6a6-1f1e895d4bf5
-- title:
--   The slit-plane preimage of a continuous function is open
-- statement:
--   The slit-plane preimage of a continuous function is open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L88

import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_localLogGoodDomain
import Definitions.Def_levy_foundations_localLogExponent

open Filter Topology

theorem levy_foundations_localLog_isOpen_goodDomain
    {E : Type*} [TopologicalSpace E] [Zero E]
    {φ : E → ℂ} (hφ_cont : Continuous φ) :
    IsOpen (LevyFoundations.LocalLog.goodDomain φ) := by sorry
