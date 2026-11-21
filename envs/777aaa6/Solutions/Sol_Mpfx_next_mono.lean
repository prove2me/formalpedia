-- Prove2me | solution 1 for Mpfx.next_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:56:23.082432+00:00
-- url     : https://prove2.me/submissions/b3dc72f4-3514-4df2-a341-ab98eb01e69d

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_FiniteFormat_format_next_eq
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_mono
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_canonicalExp_zero
import Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
attribute [local simp] Mpfx.Dyadic.coe_real_add



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {d b : _root_.Mpfx.Dyadic} (hd : 0 ≤ ((d : _root_.Mpfx.Dyadic) : ℝ))
    (hdb : ((d : _root_.Mpfx.Dyadic) : ℝ) ≤ ((b : _root_.Mpfx.Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((d : _root_.Mpfx.Dyadic) : ℝ)) :
    ((F.toFormat.next d : _root_.Mpfx.Dyadic) : ℝ) ≤ ((F.toFormat.next b : _root_.Mpfx.Dyadic) : ℝ) := by
  have hb : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ) := hd.trans hdb
  have hexp : F.canonicalExp ((d : _root_.Mpfx.Dyadic) : ℝ) ≤ F.canonicalExp ((b : _root_.Mpfx.Dyadic) : ℝ) := by
    rcases hd.lt_or_eq with hd0 | hd0
    · exact F.canonicalExp_mono hd0.ne' (by rwa [abs_of_pos hd0, abs_of_nonneg hb])
    · cases he : F.exp using QExp.recBotCoe with
      | bot => exact absurd (hguard he) (by rw [← hd0]; exact lt_irrefl 0)
      | coe e => rw [← hd0, canonicalExp_zero F he]; exact F.exp_le_canonicalExp _ he
  rw [F.format_next_eq hd hguard, F.format_next_eq hb fun he => (hguard he).trans_le hdb,
    _root_.Mpfx.Dyadic.coe_real_add, _root_.Mpfx.Dyadic.coe_real_add, coe_real_ofIntZpow_one, coe_real_ofIntZpow_one]
  linarith [zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp]
end Mpfx
