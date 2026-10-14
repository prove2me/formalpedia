-- Prove2me | Theorems.Thm_actuarial_c_frac_udd_end
-- name    : actuarial_c_frac_udd_end
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:40:25.134983+00:00
-- url     : https://prove2.me/theorems/a659c91c-4eb0-48dd-8b94-1a5439d4d4f2
-- title:
--   UDD conditional survival at the year end recovers the annual survival probability p.
-- statement:
--   UDD conditional survival at the year end recovers the annual survival probability p.
--
--   Assumptions and domains are exactly those in the Lean quantifiers. These are separate open owner-Draft statements, even when a matching source has been proved in a private diagnostic file.
-- source:
--   Original derived actuarial theorem grounded in Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7, UDD and constant-force within-year assumptions. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml. It is not a verbatim textbook Lean theorem.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_uddSurvival

open ActuarialAssurances.Fractional

theorem actuarial_c_frac_udd_end (p : ℝ) : uddSurvival p 1 = p := by sorry
