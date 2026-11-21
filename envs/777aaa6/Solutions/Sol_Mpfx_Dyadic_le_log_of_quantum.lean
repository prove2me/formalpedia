-- Prove2me | solution 1 for Mpfx.Dyadic.le_log_of_quantum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:33:40.065379+00:00
-- url     : https://prove2.me/submissions/f9b8beef-ea1e-451d-a063-b1e6164186e4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_abs_ge_two_zpow_of_quantum

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {e : ℤ} {d : Dyadic}
    (hq : quantumAtLeast (e : QExp) d) (hne : (d : ℝ) ≠ 0) :
    e ≤ Int.log 2 |(d : ℝ)| :=
  (Int.zpow_le_iff_le_log (by norm_num) (abs_pos.mpr hne)).mp
    (by exact_mod_cast abs_ge_two_zpow_of_quantum hq hne)
end Mpfx.Dyadic
