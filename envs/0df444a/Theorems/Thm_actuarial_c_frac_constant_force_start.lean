-- Prove2me | Theorems.Thm_actuarial_c_frac_constant_force_start
-- name    : actuarial_c_frac_constant_force_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:40:40.569149+00:00
-- url     : https://prove2.me/theorems/e169cc0b-cf57-4cd1-acfc-fe0246c62137
-- title:
--   Finite constant-force conditional survival starts at one at time zero.
-- statement:
--   Finite constant-force conditional survival starts at one at time zero.
--
--   Assumptions and domains are exactly those in the Lean quantifiers. These are separate open owner-Draft statements, even when a matching source has been proved in a private diagnostic file.
-- source:
--   Original derived actuarial theorem grounded in Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7, UDD and constant-force within-year assumptions. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml. It is not a verbatim textbook Lean theorem.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_cfSurvival

open ActuarialAssurances.Fractional

theorem actuarial_c_frac_constant_force_start (p : ℝ) : cfSurvival p 0 = 1 := by sorry
