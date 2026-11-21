-- Prove2me | Theorems.Thm_Fpy_Exec_ite_guard
-- name    : Fpy.Exec.ite_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:49:58.056872+00:00
-- url     : https://prove2.me/theorems/8b0df1cd-ac17-4f31-ada2-9abcbb2f808e
-- title:
--   Exec: ite guard
-- statement:
--   The Exec construction uses the ite guard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L232-L236
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L232-L236

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}

theorem Fpy.Exec.ite_guard {e : Expr L} {s₁ s₂ : Stmt L} {o : Outcome}
    (h : Exec Φ σ C (.ite e s₁ s₂) o) : ∃ b, Eval Φ σ C e (.bool b) := by sorry
