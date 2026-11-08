-- Prove2me | Theorems.Thm_levy_foundations_ceilApprox_ge
-- name    : levy_foundations_ceilApprox_ge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:49:06.706002+00:00
-- url     : https://prove2.me/theorems/f819c9d0-86e8-48de-a57f-8c915e56b50e
-- title:
--   Ceiling rational approximations lie above time
-- statement:
--   Ceiling rational approximations lie above time.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L132

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Order.Basic
import Definitions.Def_levy_foundations_ceilApprox

open Filter Topology
open scoped NNReal

theorem levy_foundations_ceilApprox_ge
    (t : ℝ≥0) (m : ℕ) :
    t ≤ LevyFoundations.DensityExtension.ceilApprox t m := by sorry
