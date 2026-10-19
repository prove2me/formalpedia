-- Prove2me | Theorems.Thm_actuarial_c_bridge_halfyear_payment_grid
-- name    : actuarial_c_bridge_halfyear_payment_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:21:57.594984+00:00
-- url     : https://prove2.me/theorems/6ec0c9af-62f3-4e99-b25f-f7c1fc19cf2d
-- title:
--   The second of two m-thly payment grid points is half a policy year
-- statement:
--   With a strictly positive two-period-per-year grid, the policy-time coordinate fractionalTime 2 1 equals exactly 1/2. This is the mathematical link between an actuarial m-thly settlement schedule and a within-year survival duration.
--
--   This theorem is an open target in the owner Draft. Its underlying mathematical statement has a separately submitted, admission-free Lean proof candidate and must still be proved against the published mission target once that target exists.
-- source:
--   Original derived formal reconciliation of m-thly cashflow timing and fractional mortality. Reference: S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 7–8. It is not a verbatim textbook statement.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_c_cont_fractionalTime

theorem actuarial_c_bridge_halfyear_payment_grid :
    ActuarialAssurances.Continuous.fractionalTime 2 1 = (1 / 2 : ℝ) := by sorry
