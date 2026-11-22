-- Prove2me | Definitions.Def_Fpy_Sum
-- name    : Fpy_Sum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:06:20.108887+00:00
-- url     : https://prove2.me/theorems/905fbd4a-1373-4450-80ad-01996f3da6a3
-- title:
--   Sum
-- statement:
--   Definitions and structural lemmas for Sum, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Sum.lean

import Definitions.Def_Fpy_Semantics
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
namespace Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
def sumLoop : Stmt (fpy decode) :=
  .whileDo (.exactOp .lt [.var "i", .exactOp .len [.var "xs"]])
    (.seq (.assign "s" (.arithOp .add [.var "s", .index (.var "xs") (.var "i")]))
      (.withCtx .real (.assign "i" (.arithOp .add [.var "i", .num (.finite 1)]))))
def sumBody : Stmt (fpy decode) :=
  .ite (.exactOp .eq [.exactOp .len [.var "xs"], .num (.finite 0)]) (.ret (.num (.finite 0)))
    (.seq (.assign "s" (.index (.var "xs") (.num (.finite 0))))
      (.seq (.assign "i" (.num (.finite 1))) (.seq sumLoop (.ret (.var "s")))))
noncomputable def sumVal (r : Num → Num) : List Num → Num
  | [] => .finite 0
  | u :: us => us.foldl (fun s w => r (Num.add s w)) u
section Run
variable {C : Val} {r : Num → Num} (hr : C.rnd (fpy decode) = some r) (us : List Num)
def sumStore (p : Num) (k : ℕ) : Store :=
  ((Store.single "xs" (.list (us.map .num))).update "s" (.num p)).update "i" (.num (.finite k))
end Run
end Fpy


