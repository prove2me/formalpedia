-- Prove2me | Theorems.Thm_Fpy_equiv_bind
-- name    : Fpy.equiv_bind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:45.589188+00:00
-- url     : https://prove2.me/theorems/ebecf4d7-a1fa-4de9-9f49-88ce754ebeb6
-- title:
--   Fpy: equiv bind
-- statement:
--   Binding `es` under `C` to fresh `ts`, as each rewrite of Fig. 12 does first:
--   a rewrite of `x = op(ts)` under `Γ[ts ↦ fmt(es)]` is one of `x = op(es)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L139-L164
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L139-L164

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}

theorem Fpy.equiv_bind (hA : A.Sound Φ) {Γ : AEnv D} {κ : Option Val} {x : Var} {op : L.ArithOp}
    {es : List (Expr L)} {ts : List Var} {as : List (AVal D)} {s' : Stmt L}
    (hts : ts.Nodup) (hl : ts.length = es.length) (hX : ∀ t ∈ ts, t ∈ X)
    (hes : ∀ e ∈ es, Avoids X e) (has : AEvalList A Φ Γ κ es as)
    (h : Equiv Φ X (updates Γ ts as) κ (.assign x (.arith op (ts.map .var))) s') :
    Equiv Φ X Γ κ (.assign x (.arith op es)) (Stmt.binds ts es s') := by sorry
