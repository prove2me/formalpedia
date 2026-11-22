-- Prove2me | Theorems.Thm_Fpy_equiv_insert
-- name    : Fpy.equiv_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:59.575793+00:00
-- url     : https://prove2.me/theorems/4834b785-4c8b-42bc-a56e-e1590e3650fb
-- title:
--   Fpy: equiv insert
-- statement:
--   **Insert**: `[R] x = op(ts) ⇝ with C' in x = op(ts)` if `fmt(tᵢ) ⊆ Fᵢ` and
--   `op♯(Fs) ⊆ F_{C'}`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L205-L212
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L205-L212

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}

theorem Fpy.equiv_insert (hA : A.Sound Φ) {Γ : AEnv D} {C' : Val} {r' : Num → Num} {FC : D.Fmt}
    {c : Expr L} {x : Var} {op : L.ArithOp} {ts : List Var} {Fs : List D.Fmt}
    (hc : Denotes Φ c C') (hr' : C'.rnd L = some r') (hFC : A.ctxFmt C' = some FC)
    (hF : FmtsIn Γ ts Fs) (hsub : D.γ (A.arith op Fs) ⊆ D.γ FC) :
    Equiv Φ X Γ (some .real) (.assign x (.arith op (ts.map .var)))
      (.withCtx c (.assign x (.arith op (ts.map .var)))) := by sorry
