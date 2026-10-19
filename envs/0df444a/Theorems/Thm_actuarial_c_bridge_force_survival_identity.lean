-- Prove2me | Theorems.Thm_actuarial_c_bridge_force_survival_identity
-- name    : actuarial_c_bridge_force_survival_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:42:28.62235+00:00
-- url     : https://prove2.me/theorems/d71f5b9d-079c-4719-9925-014a23670e25
-- title:
--   Finite constant mortality force determines within-year exponential survival
-- statement:
--   Under positive annual survival p, the constant-force survival curve exp(u log p) is exactly exp(-λu) with λ=-log p. This bridge links the actuarial force-of-mortality parameter to the fractional conditional-survival function rather than retaining an isolated parameter definition.
--
--   This theorem is an open target in the owner Draft. Its underlying mathematical statement has a separately submitted, admission-free Lean proof candidate and must still be proved against the published mission target once that target exists.
-- source:
--   Original derived formal reconciliation of m-thly cashflow timing and fractional mortality. Reference: S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 7–8. It is not a verbatim textbook statement.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_c_frac_mortalityForce
import Definitions.Def_actuarial_c_frac_cfSurvival

open ActuarialAssurances.Fractional

theorem actuarial_c_bridge_force_survival_identity (p u : ℝ) (hp : 0 < p) :
    cfSurvival p u = Real.exp (-mortalityForce p * u) := by sorry
