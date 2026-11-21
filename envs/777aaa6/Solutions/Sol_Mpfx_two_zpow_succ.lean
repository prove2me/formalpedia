-- Prove2me | solution 1 for Mpfx.two_zpow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:44.757302+00:00
-- url     : https://prove2.me/submissions/45d4202c-1659-4b0f-83a5-2bc10f8822dd

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (t : ℤ) : (2 : ℝ) ^ (t + 1) = 2 * (2 : ℝ) ^ t := by
  rw [zpow_add_one₀ (by norm_num)]; ring
end Mpfx
