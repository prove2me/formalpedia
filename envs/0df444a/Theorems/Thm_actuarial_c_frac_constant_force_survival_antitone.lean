-- Prove2me | Theorems.Thm_actuarial_c_frac_constant_force_survival_antitone
-- name    : actuarial_c_frac_constant_force_survival_antitone
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:41:32.063989+00:00
-- url     : https://prove2.me/theorems/2e2939bf-b736-425e-9d39-3edc60f1908d
-- title:
--   If 0<p≤1, the constant-force survival probability is nonincreasing with time.
-- statement:
--   If 0<p≤1, the constant-force survival probability is nonincreasing with time.
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

theorem actuarial_c_frac_constant_force_survival_antitone (p u v : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (huv : u ≤ v) :
    cfSurvival p v ≤ cfSurvival p u := by sorry
