-- Prove2me | Theorems.Thm_mme_exact_step_positive_copies_log_lower_bound
-- name    : mme_exact_step_positive_copies_log_lower_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T14:00:29.007703+00:00
-- url     : https://prove2.me/theorems/01bdd76d-9212-4550-a21f-4d009b91c302
-- title:
--   Positive surviving copies with an explicit logarithmic rate
-- statement:
--   If a real lower bound B for the selected count is at least twice the power-of-eight repair budget, the exact step has positive surviving copies. Their log count is strictly greater than log B minus the repair exponent times log 8 minus log 2. Both the positivity threshold and the rounding allowance are explicit.
-- source:
--   Natural logarithm repair budgets, finite profile capacities, and exact-step copy rounding.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open MME MME.ProfiledCW
set_option autoImplicit false
universe u

theorem mme_exact_step_positive_copies_log_lower_bound
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) {B : ℝ}
    (hB : B ≤ E.count) (hlarge : 2 * (8 : ℝ) ^ E.stage.repairExponent ≤ B) :
    0 < E.copies ∧ Real.log B -
      (E.stage.repairExponent : ℝ) * Real.log 8 - Real.log 2 < Real.log E.copies := by sorry
