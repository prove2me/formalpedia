-- Prove2me | solution 1 for Mpfx.log_abs_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:19:08.598634+00:00
-- url     : https://prove2.me/submissions/152b9091-123c-4107-95ea-8b4bdbea0d30

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Theorems.Thm_Mpfx_log_eq_of_zpow_bounds

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {k : ℤ} (hk_ne : k ≠ 0) (e' : ℤ) :
    Int.log 2 |(k : ℝ) * (2 : ℝ) ^ e'| = Int.log 2 (|k| : ℝ) + e' := by
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e' := zpow_pos two_pos e'
  have hk : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hk_ne)
  rw [abs_mul, abs_of_pos h2e]
  refine log_eq_of_zpow_bounds (mul_pos hk h2e) ?_ ?_
  · rw [zpow_add₀ two_ne_zero]
    exact mul_le_mul_of_nonneg_right (Int.zpow_log_le_self (by norm_num) hk) h2e.le
  · rw [show Int.log 2 |(k : ℝ)| + e' + 1 = (Int.log 2 |(k : ℝ)| + 1) + e' by ring,
      zpow_add₀ two_ne_zero]
    exact mul_lt_mul_of_pos_right (Int.lt_zpow_succ_log_self (by norm_num) _) h2e
end Mpfx
