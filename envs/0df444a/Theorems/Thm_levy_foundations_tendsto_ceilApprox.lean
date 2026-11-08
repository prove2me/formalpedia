-- Prove2me | Theorems.Thm_levy_foundations_tendsto_ceilApprox
-- name    : levy_foundations_tendsto_ceilApprox
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:49:35.177084+00:00
-- url     : https://prove2.me/theorems/b014f02c-b6c5-4002-98b6-bb9910c3db3d
-- title:
--   Rational ceiling approximations converge to time
-- statement:
--   Rational ceiling approximations converge to time.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L147

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Order.Basic
import Definitions.Def_levy_foundations_ceilApprox

open Filter Topology
open scoped NNReal

theorem levy_foundations_tendsto_ceilApprox
    (t : ℝ≥0) :
    Tendsto (LevyFoundations.DensityExtension.ceilApprox t) atTop (𝓝 t) := by sorry
