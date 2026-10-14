-- Prove2me | Theorems.Thm_actuarial_c_frac_constant_force_end
-- name    : actuarial_c_frac_constant_force_end
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:40:56.744976+00:00
-- url     : https://prove2.me/theorems/f617675c-71be-49fd-9cd3-93b6f5ef205e
-- title:
--   For positive p, constant-force conditional survival at time one equals p.
-- statement:
--   For positive p, constant-force conditional survival at time one equals p.
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

theorem actuarial_c_frac_constant_force_end (p : ℝ) (hp : 0 < p) :
    cfSurvival p 1 = p := by sorry
