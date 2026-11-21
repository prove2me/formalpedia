-- Prove2me | solution 1 for Mpfx.two_zpow_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:27:35.404928+00:00
-- url     : https://prove2.me/submissions/5ad0993f-ade3-4974-ba22-73366f0a5832

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Theorems.Thm_Mpfx_two_zpow_dbl

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (a : ℤ) : (2 : ℝ) ^ a / 2 = (2 : ℝ) ^ (a - 1) := by
  rw [two_zpow_dbl a]; ring
end Mpfx
