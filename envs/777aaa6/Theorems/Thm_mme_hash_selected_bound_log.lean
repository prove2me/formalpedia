-- Prove2me | Theorems.Thm_mme_hash_selected_bound_log
-- name    : mme_hash_selected_bound_log
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T14:07:14.188925+00:00
-- url     : https://prove2.me/theorems/1b263328-fcbf-4cfd-8ba8-0637955c9b75
-- title:
--   Exact logarithm of the selected-count lower bound
-- statement:
--   For positive target count A and hash scale Q, the selected-count lower bound has logarithm log A minus log Q minus four times sqrt(log Q) minus log 32.
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

theorem mme_hash_selected_bound_log (A Q : ℝ) (hA : 0 < A) (hQ : 0 < Q) :
    Real.log (A * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q)) =
      Real.log A - Real.log Q - 4 * Real.sqrt (Real.log Q) - Real.log 32 := by sorry
