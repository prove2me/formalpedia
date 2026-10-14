-- Prove2me | Theorems.Thm_actuarial_c_frac_udd_cf_halfyear_gap_square
-- name    : actuarial_c_frac_udd_cf_halfyear_gap_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:39:24.23941+00:00
-- url     : https://prove2.me/theorems/6901e63c-e7e2-42e0-857b-3cb7985287c8
-- title:
--   Exact nonnegative-square expression for the difference between UDD and constant-force survival at half a year.
-- statement:
--   Exact nonnegative-square expression for the difference between UDD and constant-force survival at half a year.
--
--   Assumptions and domains are exactly those in the Lean quantifiers. These are separate open owner-Draft statements, even when a matching source has been proved in a private diagnostic file.
-- source:
--   Original derived actuarial theorem grounded in Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7, UDD and constant-force within-year assumptions. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml. It is not a verbatim textbook Lean theorem.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_uddHalf
import Definitions.Def_actuarial_c_frac_cfHalf

open ActuarialAssurances.Fractional

theorem actuarial_c_frac_udd_cf_halfyear_gap_square (p : ℝ) (hp : 0 ≤ p) :
    uddHalf p - cfHalf p = (Real.sqrt p - 1)^2 / 2 := by sorry
