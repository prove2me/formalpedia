-- Prove2me | Theorems.Thm_ReweightedNPMLE_log_one_add_sq_le_two_sq
-- name    : ReweightedNPMLE.log_one_add_sq_le_two_sq
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:44:38.721139+00:00
-- url     : https://prove2.me/theorems/c743f260-a2fa-4539-8c25-0560af9aa161
-- title:
--   Squared logarithmic displacement on the localization ball
-- statement:
--   For $u\in\mathbb R$ with $|u|\le1/16$, $$[\log(1+u)]^2\le2u^2.$$ This converts localized relative fitted-vector error into the unnormalized sum of squared fitted log-ratios.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Localization.lean#L28-L44

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set

theorem ReweightedNPMLE.log_one_add_sq_le_two_sq {u : ℝ} (hu : |u| ≤ 1 / 16) :
    Real.log (1 + u) ^ 2 ≤ 2 * u ^ 2 := by sorry
