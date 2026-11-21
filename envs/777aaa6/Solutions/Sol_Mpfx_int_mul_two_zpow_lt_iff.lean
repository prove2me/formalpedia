-- Prove2me | solution 1 for Mpfx.int_mul_two_zpow_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:58.864187+00:00
-- url     : https://prove2.me/submissions/0730799e-2433-4cb0-9e24-257661a899da

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {a b k : ℤ} :
    (a : ℝ) * (2 : ℝ) ^ k < (b : ℝ) * (2 : ℝ) ^ k ↔ a < b := by
  rw [mul_lt_mul_iff_of_pos_right (zpow_pos two_pos k)]; exact Int.cast_lt
end Mpfx
