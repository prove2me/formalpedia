-- Prove2me | Theorems.Thm_levy_foundations_tendsto_ceilApprox_nhdsWithin_Ici
-- name    : levy_foundations_tendsto_ceilApprox_nhdsWithin_Ici
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:49:44.426215+00:00
-- url     : https://prove2.me/theorems/350783dd-a7ed-4da1-b5c7-1b3a50c8cf70
-- title:
--   Ceiling approximations converge from the right
-- statement:
--   Ceiling approximations converge from the right.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L169

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Order.Basic
import Definitions.Def_levy_foundations_ceilApprox

open Filter Topology
open scoped NNReal

theorem levy_foundations_tendsto_ceilApprox_nhdsWithin_Ici
    (t : ℝ≥0) :
    Tendsto (LevyFoundations.DensityExtension.ceilApprox t) atTop (𝓝[≥] t) := by sorry
