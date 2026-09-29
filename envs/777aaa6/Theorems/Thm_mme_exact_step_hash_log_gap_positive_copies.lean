-- Prove2me | Theorems.Thm_mme_exact_step_hash_log_gap_positive_copies
-- name    : mme_exact_step_hash_log_gap_positive_copies
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T14:06:54.14953+00:00
-- url     : https://prove2.me/theorems/3873d969-01e6-4538-a10d-f7b1293d5d63
-- title:
--   A hash log gap guarantees positive repaired copies
-- statement:
--   For an exact step whose selected count dominates A exp(-4 sqrt(log Q))/(32 Q), an explicit logarithmic gap covering the repair cost and log 32 plus log 2 guarantees positive repaired copies and a strict lower bound on their logarithm. Positivity of A and Q and the log-gap hypothesis are required.
-- source:
--   Selected-count logarithms and uniformly controlled repair for the concrete released regional extraction.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open MME MME.ProfiledCW
set_option autoImplicit false
universe u

theorem mme_exact_step_hash_log_gap_positive_copies
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P)
    (A Q : ℝ) (hA : 0 < A) (hQ : 0 < Q)
    (hcount : A * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count)
    (hgap : Real.log 32 + Real.log 2 +
      (E.stage.repairExponent : ℝ) * Real.log 8 ≤
      Real.log A - Real.log Q - 4 * Real.sqrt (Real.log Q)) :
    0 < E.copies ∧ Real.log A - Real.log Q - 4 * Real.sqrt (Real.log Q) -
      (E.stage.repairExponent : ℝ) * Real.log 8 - Real.log 32 - Real.log 2 <
        Real.log E.copies := by sorry
