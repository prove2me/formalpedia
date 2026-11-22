-- Prove2me | Theorems.Thm_Fpy_equiv_reround
-- name    : Fpy.equiv_reround
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:32:12.19118+00:00
-- url     : https://prove2.me/theorems/977d6e8b-d39e-416c-beb6-11edd96ca0c5
-- title:
--   Fpy: equiv reround
-- statement:
--   Rounding `op(ys)` under `C'` (denoted by `c`) instead of `C`: correct when
--   both round each exact result the same way, for the values of `ys` in `Γ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L170-L190
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L170-L190

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}

theorem Fpy.equiv_reround {Γ : AEnv D} {C C' : Val} {r r' : Num → Num} {c : Expr L} {x : Var}
    {op : L.ArithOp} {ys : List Var} (hc : Denotes Φ c C') (hr : C.rnd L = some r)
    (hr' : C'.rnd L = some r')
    (h : ∀ σ ns n, Γ.Holds σ → List.Forall₂ (fun y n => σ y = some (.num n)) ys ns →
      L.arith op ns = some n → r n = r' n) :
    Equiv Φ X Γ (some C) (.assign x (.arith op (ys.map .var)))
      (.withCtx c (.assign x (.arith op (ys.map .var)))) := by sorry
