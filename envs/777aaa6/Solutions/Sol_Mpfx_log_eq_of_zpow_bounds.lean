-- Prove2me | solution 1 for Mpfx.log_eq_of_zpow_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:18:16.224804+00:00
-- url     : https://prove2.me/submissions/2c4771d2-ae45-4c95-9e8f-1d9f3d4e0ca5

import Mathlib.Tactic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {x : ℝ} {k : ℤ} (hx : 0 < x)
    (hlo : (2 : ℝ) ^ k ≤ x) (hhi : x < (2 : ℝ) ^ (k + 1)) : Int.log 2 x = k := by
  have h1 : k ≤ Int.log 2 x :=
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hx).mp (by exact_mod_cast hlo)
  have h2 : Int.log 2 x < k + 1 :=
    (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hx).mp (by exact_mod_cast hhi)
  omega
end Mpfx
