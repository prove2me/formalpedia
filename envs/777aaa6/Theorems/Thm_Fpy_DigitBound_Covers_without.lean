-- Prove2me | Theorems.Thm_Fpy_DigitBound_Covers_without
-- name    : Fpy.DigitBound.Covers.without
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:26:22.65851+00:00
-- url     : https://prove2.me/theorems/37798968-aa59-4670-8285-295e900bb0e9
-- title:
--   Covers: without
-- statement:
--   Variables outside `X` keep their description.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Join.lean#L65-L68
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Join.lean#L65-L68

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Join
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_without

set_option autoImplicit true
open Fpy Fpy.DigitBound

theorem Fpy.DigitBound.Covers.without {D : FormatDomain} {Ψg : List Con} (n : ℕ) (X : List Var) (Γᵢ : AEnv D)
    (Δ : DEnv) : Covers n n Ψg [] X Γᵢ Δ (Δ.without X) := by sorry
