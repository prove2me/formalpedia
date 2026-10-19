-- Prove2me | Theorems.Thm_actuarial_c_frac_udd_half_agrees_with_time_model
-- name    : actuarial_c_frac_udd_half_agrees_with_time_model
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:41:52.355329+00:00
-- url     : https://prove2.me/theorems/eaf4a738-ba07-412c-b489-1b857062ef2e
-- title:
--   The UDD linear survival curve evaluated at half a year equals the direct half-year formula.
-- statement:
--   The UDD linear survival curve evaluated at half a year equals the direct half-year formula.
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
import Definitions.Def_actuarial_c_frac_uddSurvival

open ActuarialAssurances.Fractional

theorem actuarial_c_frac_udd_half_agrees_with_time_model (p : ℝ) :
    uddSurvival p (1 / 2) = uddHalf p := by sorry
