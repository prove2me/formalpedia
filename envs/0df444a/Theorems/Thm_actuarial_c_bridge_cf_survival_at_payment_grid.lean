-- Prove2me | Theorems.Thm_actuarial_c_bridge_cf_survival_at_payment_grid
-- name    : actuarial_c_bridge_cf_survival_at_payment_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:22:30.546986+00:00
-- url     : https://prove2.me/theorems/2f9413b0-f7d5-40df-8584-f01f460ecaae
-- title:
--   Constant-force half-year survival equals survival evaluated at the cashflow grid
-- statement:
--   For strictly positive annual survival p, evaluating the continuous constant-force survival curve at the payment coordinate 1/2 equals the positive square-root half-year survival. The proof must exclude fictitious finite constant force at p=0.
--
--   This theorem is an open target in the owner Draft. Its underlying mathematical statement has a separately submitted, admission-free Lean proof candidate and must still be proved against the published mission target once that target exists.
-- source:
--   Original derived formal reconciliation of m-thly cashflow timing and fractional mortality. Reference: S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 7–8. It is not a verbatim textbook statement.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_frac_cfSurvival
import Definitions.Def_actuarial_c_frac_cfHalf

open ActuarialAssurances.Fractional

theorem actuarial_c_bridge_cf_survival_at_payment_grid (p : ℝ) (hp : 0 < p) :
    cfSurvival p (ActuarialAssurances.Continuous.fractionalTime 2 1) =
      cfHalf p := by sorry
