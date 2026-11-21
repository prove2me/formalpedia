-- Prove2me | solution 1 for Mpfx.FiniteFormat.abs_lt_of_mul_zpow_canonicalExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:53:32.372185+00:00
-- url     : https://prove2.me/submissions/9f056705-c692-4042-a5db-95779b0ab127

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_FiniteFormat_log_sub_p_le_canonicalExp
import Theorems.Thm_Mpfx_abs_mul_two_zpow


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace FiniteFormat
theorem _root_.solution (F : FiniteFormat) {p : ℕ}
    (hp : F.p = (p : Prec)) {x : ℝ} (hx : x ≠ 0) {m : ℤ}
    (h : x = m * (2 : ℝ) ^ F.canonicalExp x) : |m| < 2 ^ p := by
  have hc := F.log_sub_p_le_canonicalExp hx hp
  have hlt : |x| < (2 : ℝ) ^ (Int.log 2 |x| + 1) := Int.lt_zpow_succ_log_self (by norm_num) _
  have h1 : |(m : ℝ)| * (2 : ℝ) ^ F.canonicalExp x
      < (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ F.canonicalExp x := by
    rw [← abs_mul_two_zpow, ← h, ← zpow_add₀ two_ne_zero]
    exact hlt.trans_le (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have h2 := lt_of_mul_lt_mul_right h1 (zpow_pos two_pos _).le
  rw [zpow_natCast] at h2
  exact_mod_cast h2
end FiniteFormat
end Mpfx
