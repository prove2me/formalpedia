-- Prove2me | solution 1 for Mpfx.FiniteFormat.canonicalExp_shrink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:25.266113+00:00
-- url     : https://prove2.me/submissions/86c05ac7-35b9-4b8a-8312-69d930c9dcbb

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_FiniteFormat_shrink_exp_coe
import Theorems.Thm_Mpfx_FiniteFormat_shrink_exp_bot
import Theorems.Thm_Mpfx_FiniteFormat_p_pos
import Theorems.Thm_Mpfx_canonicalExp_expBot
import Theorems.Thm_Mpfx_canonicalExp_expFinite
import Theorems.Thm_Mpfx_canonicalExp_pTop


set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) (h : F.p ≠ ((1 : ℕ) : Prec)) {x : ℝ}
    (hx : x ≠ 0) : (F.shrink h).canonicalExp x = F.canonicalExp x + 1 := by
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    cases hexp : F.exp using QExp.recBotCoe with
    | bot => exact (F.finite.elim (· hp) (· hexp)).elim
    | coe e =>
      rw [canonicalExp_pTop hp hexp, canonicalExp_pTop (F := F.shrink h)
        (by change F.p - 1 = ⊤; rw [hp]; rfl) (shrink_exp_coe h hexp)]
  | coe n =>
    have h0 := F.p_pos hp
    have h1 : n ≠ 1 := fun h1 => h (by rw [hp, h1])
    have hpc : (F.shrink h).p = ((n - 1 : ℕ) : Prec) := by
      change F.p - 1 = _; rw [hp]; norm_cast
    have hcast : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
    cases hexp : F.exp using QExp.recBotCoe with
    | bot =>
      rw [canonicalExp_expBot hp hexp hx, canonicalExp_expBot hpc
        (shrink_exp_bot h hexp) hx, hcast]
      ring
    | coe e =>
      rw [canonicalExp_expFinite hp hexp hx, canonicalExp_expFinite hpc
        (shrink_exp_coe h hexp) hx, hcast]
      omega
end Mpfx.FiniteFormat
