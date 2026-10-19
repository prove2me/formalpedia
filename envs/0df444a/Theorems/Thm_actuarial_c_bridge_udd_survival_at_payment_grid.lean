-- Prove2me | Theorems.Thm_actuarial_c_bridge_udd_survival_at_payment_grid
-- name    : actuarial_c_bridge_udd_survival_at_payment_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:22:16.737896+00:00
-- url     : https://prove2.me/theorems/2488966a-8106-4ab0-9a3e-9ca4e3eec3c2
-- title:
--   UDD half-year survival equals survival evaluated at the cashflow grid
-- statement:
--   Evaluating the UDD linear within-year survival curve at the 2-mthly policy payment coordinate 1/2 gives the same conditional survival value as the UDD half-year closed formula (1+p)/2.
--
--   This theorem is an open target in the owner Draft. Its underlying mathematical statement has a separately submitted, admission-free Lean proof candidate and must still be proved against the published mission target once that target exists.
-- source:
--   Original derived formal reconciliation of m-thly cashflow timing and fractional mortality. Reference: S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 7–8. It is not a verbatim textbook statement.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_frac_uddSurvival
import Definitions.Def_actuarial_c_frac_uddHalf

open ActuarialAssurances.Fractional

theorem actuarial_c_bridge_udd_survival_at_payment_grid (p : ℝ) :
    uddSurvival p (ActuarialAssurances.Continuous.fractionalTime 2 1) =
      uddHalf p := by sorry
