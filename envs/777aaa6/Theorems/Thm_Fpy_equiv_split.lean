-- Prove2me | Theorems.Thm_Fpy_equiv_split
-- name    : Fpy.equiv_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:38:02.140432+00:00
-- url     : https://prove2.me/theorems/f8deef01-af51-4f5d-ae22-1b81b716f6e0
-- title:
--   Fpy: equiv split
-- statement:
--   **Split**: `[C] x = op(ts) ⇝ with C' in r = op(ts); x = round(r)` if
--   `fmt(tᵢ) ⊆ Fᵢ` and `C(C'(v)) = C(v)` on `op(Fs)`, the exact results of `op` on
--   inputs `uᵢ ∈ Fᵢ`. `rd` is any operator computing the identity.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L219-L244
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L219-L244

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}

theorem Fpy.equiv_split {Γ : AEnv D} {C C' : Val} {rC rC' : Num → Num} {c : Expr L} {x r : Var}
    {op rd : L.ArithOp} {ts : List Var} {Fs : List D.Fmt} (hc : Denotes Φ c C')
    (hr : C.rnd L = some rC) (hr' : C'.rnd L = some rC') (hrd : ∀ u, L.arith rd [u] = some u)
    (hF : FmtsIn Γ ts Fs)
    (h : ∀ us n, List.Forall₂ (fun u F => u ∈ D.γ F) us Fs → L.arith op us = some n →
      rC (rC' n) = rC n) :
    Equiv Φ {r} Γ (some C) (.assign x (.arith op (ts.map .var)))
      (.seq (.withCtx c (.assign r (.arith op (ts.map .var))))
        (.assign x (.arith rd [.var r]))) := by sorry
