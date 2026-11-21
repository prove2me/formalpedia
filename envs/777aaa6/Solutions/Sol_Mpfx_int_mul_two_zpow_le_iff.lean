-- Prove2me | solution 1 for Mpfx.int_mul_two_zpow_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:30.620013+00:00
-- url     : https://prove2.me/submissions/b3564bfe-c2e7-4526-acf0-a3a3e92f2ab1

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {a b k : ℤ} :
    (a : ℝ) * (2 : ℝ) ^ k ≤ (b : ℝ) * (2 : ℝ) ^ k ↔ a ≤ b := by
  rw [mul_le_mul_iff_of_pos_right (zpow_pos two_pos k)]; exact Int.cast_le
end Mpfx
