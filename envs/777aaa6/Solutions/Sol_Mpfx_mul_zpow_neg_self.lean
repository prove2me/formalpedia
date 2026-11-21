-- Prove2me | solution 1 for Mpfx.mul_zpow_neg_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:05.480292+00:00
-- url     : https://prove2.me/submissions/25d84f9c-b223-43af-8e68-a46d053e60c8

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (x : ℝ) (e : ℤ) :
    x * (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = x := by
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      neg_add_cancel, zpow_zero, mul_one]
end Mpfx
