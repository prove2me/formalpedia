-- Prove2me | Theorems.Thm_actuarial_c_frac_mortality_force_nonnegative
-- name    : actuarial_c_frac_mortality_force_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:41:15.304425+00:00
-- url     : https://prove2.me/theorems/cbc654a1-b89d-4fa5-a8b2-315c475f91c0
-- title:
--   If 0<p≤1, the finite constant mortality force -log(p) is nonnegative.
-- statement:
--   If 0<p≤1, the finite constant mortality force -log(p) is nonnegative.
--
--   Assumptions and domains are exactly those in the Lean quantifiers. These are separate open owner-Draft statements, even when a matching source has been proved in a private diagnostic file.
-- source:
--   Original derived actuarial theorem grounded in Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7, UDD and constant-force within-year assumptions. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml. It is not a verbatim textbook Lean theorem.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_mortalityForce

open ActuarialAssurances.Fractional

theorem actuarial_c_frac_mortality_force_nonnegative (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ mortalityForce p := by sorry
