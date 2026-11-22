-- Prove2me | Theorems.Thm_Fpy_equiv_elim
-- name    : Fpy.equiv_elim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:49.91718+00:00
-- url     : https://prove2.me/theorems/54698d8c-c4df-4f64-9813-094b7200951c
-- title:
--   Fpy: equiv elim
-- statement:
--   **Elim**: `[C] x = op(ts) ⇝ with R in x = op(ts)` if `fmt(tᵢ) ⊆ Fᵢ` and
--   `op♯(Fs) ⊆ F_C`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L194-L201
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L194-L201

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}

theorem Fpy.equiv_elim (hA : A.Sound Φ) {Γ : AEnv D} {C : Val} {r : Num → Num} {FC : D.Fmt}
    {x : Var} {op : L.ArithOp} {ts : List Var} {Fs : List D.Fmt}
    (hr : C.rnd L = some r) (hFC : A.ctxFmt C = some FC) (hF : FmtsIn Γ ts Fs)
    (hsub : D.γ (A.arith op Fs) ⊆ D.γ FC) :
    Equiv Φ X Γ (some C) (.assign x (.arith op (ts.map .var)))
      (.withCtx .real (.assign x (.arith op (ts.map .var)))) := by sorry
