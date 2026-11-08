-- Prove2me | Theorems.Thm_levy_foundations_ceilApprox_coe
-- name    : levy_foundations_ceilApprox_coe
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:49:19.270007+00:00
-- url     : https://prove2.me/theorems/0ed8373d-a67e-4795-8852-8a4657605671
-- title:
--   Coerce the rational ceiling approximation to reals
-- statement:
--   Coerce the rational ceiling approximation to reals.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L140

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Order.Basic
import Definitions.Def_levy_foundations_ceilApprox

open Filter Topology
open scoped NNReal

theorem levy_foundations_ceilApprox_coe
    (t : ℝ≥0) (m : ℕ) :
    (LevyFoundations.DensityExtension.ceilApprox t m : ℝ) =
      ↑⌈(t : ℝ) * ↑(m + 1)⌉₊ / ↑(m + 1) := by sorry
