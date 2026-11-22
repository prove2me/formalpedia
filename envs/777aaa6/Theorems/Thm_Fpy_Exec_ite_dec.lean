-- Prove2me | Theorems.Thm_Fpy_Exec_ite_dec
-- name    : Fpy.Exec.ite_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:02:00.750835+00:00
-- url     : https://prove2.me/theorems/41eea8b3-fd33-4e63-894f-cb5bc9546eed
-- title:
--   Exec: ite dec
-- statement:
--   The Exec construction uses the ite dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L238-L243
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L238-L243

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}

theorem Fpy.Exec.ite_dec {e : Expr L} {s₁ s₂ : Stmt L} {o : Outcome} {b : Prop} [Decidable b]
    (he : Eval Φ σ C e (.bool (decide b))) (h₁ : b → Exec Φ σ C s₁ o)
    (h₂ : ¬ b → Exec Φ σ C s₂ o) : Exec Φ σ C (.ite e s₁ s₂) o := by sorry
