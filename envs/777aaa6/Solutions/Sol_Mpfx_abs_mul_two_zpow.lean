-- Prove2me | solution 1 for Mpfx.abs_mul_two_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:15.709215+00:00
-- url     : https://prove2.me/submissions/a016c534-3178-47da-a460-e5f6d2ae35d3

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (c : ℝ) (e : ℤ) :
    |c * (2 : ℝ) ^ e| = |c| * (2 : ℝ) ^ e := by
  rw [abs_mul, abs_zpow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
end Mpfx
