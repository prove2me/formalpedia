-- Prove2me | Theorems.Thm_Fpy_DigitBound_Con_P_ext
-- name    : Fpy.DigitBound.Con.P_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:10:51.827567+00:00
-- url     : https://prove2.me/theorems/be5fdaf3-34fd-45e9-8537-95641e9c892d
-- title:
--   Con: P ext
-- statement:
--   The Con construction uses the P ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L302-L305
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L302-L305

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_Ops
import Mathlib.Order.WithBotTop
import Definitions.Def_Fpy_DigitBound_Defs
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}

theorem Fpy.DigitBound.Con.P_ext {v : ℕ} {ge : Bool} {τ₁ τ₂ : Term} {h₁ : τ₁.Below v} {h₂ : τ₂.Below v}
    {ι : Asgn} : (Con.ext v ge τ₁ τ₂ h₁ h₂).P ι ↔
      if ge then τ₁.eval ι ≤ ι v ∧ τ₂.eval ι ≤ ι v else ι v ≤ τ₁.eval ι ∧ ι v ≤ τ₂.eval ι := by sorry
