-- Prove2me | Theorems.Thm_Fpy_exec_binds
-- name    : Fpy.exec_binds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:33:40.61974+00:00
-- url     : https://prove2.me/theorems/b461b9c4-4af8-4e6a-9add-edaa859d4b94
-- title:
--   Fpy: exec binds
-- statement:
--   Binding `es` to `ts` avoided by `es` evaluates `es` in the first store.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L109-L133
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L109-L133

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}

theorem Fpy.exec_binds {C : Val} {s : Stmt L} {o : Outcome} :
    ∀ {σ : Store} {ts : List Var} {es : List (Expr L)}, ts.length = es.length →
      (∀ t ∈ ts, t ∈ X) → (∀ e ∈ es, Avoids X e) →
      (Exec Φ σ C (Stmt.binds ts es s) o ↔
        ∃ vs, EvalList Φ σ C es vs ∧ Exec Φ (updates σ ts vs) C s o)
  := by sorry
