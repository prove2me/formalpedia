-- Prove2me | solution 1 for Fpy.quantumAtLeast_of_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:47.582569+00:00
-- url     : https://prove2.me/submissions/1c546ef4-fda8-4e96-a2eb-86b719e7c92b

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe_real
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_anti
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_abs_mul_two_zpow


set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}
namespace Fpy
theorem _root_.solution {p : ℕ} {k : ℤ} {d : Mpfx.Dyadic}
    (hp : Dyadic.precisionAtMost (p : Prec) d) (hd : (d : ℝ) ≠ 0)
    (hk : k ≤ Int.log 2 |(d : ℝ)|) : Dyadic.quantumAtLeast ((k - p + 1 : ℤ) : QExp) d := by
  obtain ⟨c, e, hde, hc⟩ := (Dyadic.precisionAtMost_coe_real p d).mp hp
  by_cases he : k - p + 1 ≤ e
  · exact Dyadic.quantumAtLeast_anti (WithBot.coe_le_coe.mpr he)
      ((Dyadic.quantumAtLeast_coe_real e d).mpr ⟨c, hde⟩)
  · exfalso
    have h2k : (2 : ℝ) ^ k ≤ |(d : ℝ)| :=
      (Int.zpow_le_iff_le_log (by norm_num) (abs_pos.mpr hd)).mpr hk
    have hcR : |(c : ℝ)| < (2 : ℝ) ^ (p : ℤ) := by
      rw [zpow_natCast, ← Int.cast_abs]
      exact_mod_cast hc
    have : |(d : ℝ)| < (2 : ℝ) ^ k := by
      rw [hde, abs_mul_two_zpow]
      calc |(c : ℝ)| * (2 : ℝ) ^ e < (2 : ℝ) ^ (p : ℤ) * (2 : ℝ) ^ e :=
            mul_lt_mul_of_pos_right hcR (zpow_pos (by norm_num) _)
        _ = (2 : ℝ) ^ ((p : ℤ) + e) := (zpow_add₀ (by norm_num) _ _).symm
        _ ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
end Fpy
