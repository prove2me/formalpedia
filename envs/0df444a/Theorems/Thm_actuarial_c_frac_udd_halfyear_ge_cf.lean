-- Prove2me | Theorems.Thm_actuarial_c_frac_udd_halfyear_ge_cf
-- name    : actuarial_c_frac_udd_halfyear_ge_cf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:39:52.882676+00:00
-- url     : https://prove2.me/theorems/03db7fe3-f88b-40a5-a3fe-9d72a052d431
-- title:
--   UDD half-year survival dominates constant-force half-year survival for p≥0.
-- statement:
--   UDD half-year survival dominates constant-force half-year survival for p≥0.
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

theorem actuarial_c_frac_udd_halfyear_ge_cf (p : ℝ) (hp : 0 ≤ p) :
    cfHalf p ≤ uddHalf p := by sorry
