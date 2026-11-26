-- Prove2me | Theorems.Thm_ReweightedNPMLE_log_one_add_le_sub_sq_third
-- name    : ReweightedNPMLE.log_one_add_le_sub_sq_third
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:44:41.392083+00:00
-- url     : https://prove2.me/theorems/05fa91ae-7782-4c6b-914d-a46176a97c2c
-- title:
--   Quadratic upper logarithm bound for radial localization
-- statement:
--   For $u\in\mathbb R$ with $|u|\le1/4$, $$\log(1+u)\le u-u^2/3.$$ The negative quadratic term forces sufficiently near-optimal fitted vectors into the localization region.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Localization.lean#L52-L75

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set

theorem ReweightedNPMLE.log_one_add_le_sub_sq_third {u : ℝ} (hu : |u| ≤ 1 / 4) :
    Real.log (1 + u) ≤ u - u ^ 2 / 3 := by sorry
