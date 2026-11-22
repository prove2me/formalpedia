-- Prove2me | Definitions.Def_Fpy_Rewrite_Lower
-- name    : Fpy_Rewrite_Lower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:31:49.244887+00:00
-- url     : https://prove2.me/theorems/5079eb33-2e45-4fdd-9350-8c6b816e5011
-- title:
--   Lower
-- statement:
--   Definitions and structural lemmas for Lower, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg

set_option autoImplicit true
namespace Fpy
open Mpfx
namespace RoundCtx
structure Scaled (c c₀ : RoundCtx) (k : ℤ) : Prop where
  p : c.F.p = ⊤
  exp : c.F.exp = (k : QExp)
  p₀ : c₀.F.p = ⊤
  exp₀ : c₀.F.exp = ((0 : ℤ) : QExp)
  rm : c₀.rm = c.rm
  bound : ∀ y y₀ : Mpfx.Dyadic, (y : ℝ) = 2 ^ k * y₀ →
    (Format.boundOK c.F.b y ↔ Format.boundOK c₀.F.b y₀)
  special : ∀ s, (c.S.map s).toReal = Num.mul (.finite (2 ^ k)) (c₀.S.map s).toReal
  overflow : ∀ neg, (c.O.map neg).toReal = Num.mul (.finite (2 ^ k)) (c₀.O.map neg).toReal
end RoundCtx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}
def cmpOp (s : Bool) : ExactOp := bif s then .lt else .le
noncomputable def numCmp (s : Bool) (u v : Num) : Bool := bif s then Num.lt u v else Num.le u v
def nanBranch (r : Num → Num) (kn : Bool) (x t : Var) (s : Stmt (fpy decode)) :
    Stmt (fpy decode) :=
  bif kn then .ite (.exactOp .isNaN [.var t]) (.assign x (.num (r (.special .nan)))) s else s
def eqBranch (k : Bool) (x t : Var) (c d : Num) (s : Stmt (fpy decode)) : Stmt (fpy decode) :=
  bif k then .ite (.exactOp .eq [.var t, .num c]) (.assign x (.num d)) s else s
def qexpNum (e : QExp) : Num :=
  QExp.recBotCoe (C := fun _ => Num) (.special (.inf true)) (fun k => .finite k) e
end Fpy


