-- Prove2me | Theorems.Thm_ReweightedNPMLE_log_one_add_ge_sub_sq
-- name    : ReweightedNPMLE.log_one_add_ge_sub_sq
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:23.987652+00:00
-- url     : https://prove2.me/theorems/9774210a-fe84-5b4d-862b-dcf78e66754e
-- title:
--   Quadratic lower logarithm bound at radius one eighth
-- statement:
--   For $u\in\mathbb R$ with $|u|\le1/8$, $$u-u^2\le\log(1+u).$$ This lower bound controls the Gamma density ratio in the change-of-variables argument.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Localization.lean#L77-L142

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set

theorem ReweightedNPMLE.log_one_add_ge_sub_sq {u : ℝ} (hu : |u| ≤ 1 / 8) :
    u - u ^ 2 ≤ Real.log (1 + u) := by sorry
