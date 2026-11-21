-- Prove2me | Theorems.Thm_Fpy_Exec_seq_left
-- name    : Fpy.Exec.seq_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:12.837664+00:00
-- url     : https://prove2.me/theorems/134c7548-68ad-4411-9b62-38412efd9d96
-- title:
--   Exec: seq left
-- statement:
--   The Exec construction uses the seq left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L226-L230
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L226-L230

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {Φ : Program L} {σ : Store} {C : Val}

theorem Fpy.Exec.seq_left {s₁ s₂ : Stmt L} {o : Outcome} (h : Exec Φ σ C (.seq s₁ s₂) o) :
    ∃ o₁, Exec Φ σ C s₁ o₁ := by sorry
