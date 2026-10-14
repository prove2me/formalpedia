-- Prove2me | Theorems.Thm_actuarial_c_frac_cf_half_agrees_with_time_model
-- name    : actuarial_c_frac_cf_half_agrees_with_time_model
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:42:10.939988+00:00
-- url     : https://prove2.me/theorems/7edde699-f076-45a1-9766-1f53719975a1
-- title:
--   For p>0, the exponential constant-force survival curve at half a year equals sqrt(p).
-- statement:
--   For p>0, the exponential constant-force survival curve at half a year equals sqrt(p).
--
--   Assumptions and domains are exactly those in the Lean quantifiers. These are separate open owner-Draft statements, even when a matching source has been proved in a private diagnostic file.
-- source:
--   Original derived actuarial theorem grounded in Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7, UDD and constant-force within-year assumptions. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml. It is not a verbatim textbook Lean theorem.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_cfHalf
import Definitions.Def_actuarial_c_frac_cfSurvival

open ActuarialAssurances.Fractional

theorem actuarial_c_frac_cf_half_agrees_with_time_model (p : ℝ) (hp : 0 < p) :
    cfSurvival p (1 / 2) = cfHalf p := by sorry
