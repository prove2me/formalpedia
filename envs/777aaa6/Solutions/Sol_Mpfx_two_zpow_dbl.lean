-- Prove2me | solution 1 for Mpfx.two_zpow_dbl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:19:19.739317+00:00
-- url     : https://prove2.me/submissions/2312b068-e6ea-4143-8356-15860b55d18d

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Theorems.Thm_Mpfx_two_zpow_succ

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (a : ℤ) : (2 : ℝ) ^ a = 2 * (2 : ℝ) ^ (a - 1) := by
  rw [← two_zpow_succ, sub_add_cancel]
end Mpfx
