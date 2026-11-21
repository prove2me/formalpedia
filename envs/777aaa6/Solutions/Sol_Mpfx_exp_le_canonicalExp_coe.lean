-- Prove2me | solution 1 for Mpfx.exp_le_canonicalExp_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:39:43.517463+00:00
-- url     : https://prove2.me/submissions/4a6e4294-ec17-4de6-b775-2d5a4db374f7

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) :
    F.exp ≤ ((F.canonicalExp x : ℤ) : QExp) := by
  cases hexp : F.exp using QExp.recBotCoe with
  | bot => exact bot_le
  | coe e => exact_mod_cast F.exp_le_canonicalExp x hexp
end Mpfx
