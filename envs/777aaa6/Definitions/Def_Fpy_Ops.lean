-- Prove2me | Definitions.Def_Fpy_Ops
-- name    : Fpy_Ops
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:05:45.583181+00:00
-- url     : https://prove2.me/theorems/6b464989-5f96-4522-b7d4-8d1569c25c4c
-- title:
--   Ops
-- statement:
--   Definitions and structural lemmas for Ops, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg

set_option autoImplicit true
namespace Fpy
open Mpfx
namespace Num
noncomputable def add : Num → Num → Num
  | .finite x, .finite y => .finite (x + y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf a), .special (.inf b) => if a = b then .special (.inf a) else .special .nan
  | .special (.inf a), .finite _ | .finite _, .special (.inf a) => .special (.inf a)
noncomputable def mul : Num → Num → Num
  | .finite x, .finite y => .finite (x * y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf a), .special (.inf b) => .special (.inf (xor a b))
  | .special (.inf a), .finite y | .finite y, .special (.inf a) =>
      if y = 0 then .special .nan else .special (.inf (xor a (decide (y < 0))))
def neg : Num → Num := WithSpecial.neg
noncomputable def sub (u v : Num) : Num := add u (neg v)
noncomputable def div : Num → Num → Num
  | .finite x, .finite y =>
      if y = 0 then (if x = 0 then .special .nan else .special (.inf (decide (x < 0))))
      else .finite (x / y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf _), .special (.inf _) => .special .nan
  | .special (.inf a), .finite y => .special (.inf (xor a (decide (y < 0))))
  | .finite _, .special (.inf _) => .finite 0
noncomputable def sqrt : Num → Num
  | .finite x => if x < 0 then .special .nan else .finite (Real.sqrt x)
  | .special (.inf false) => .special (.inf false)
  | .special _ => .special .nan
noncomputable def fma (u v w : Num) : Num := add (mul u v) w
noncomputable def abs : Num → Num
  | .finite x => .finite |x|
  | .special (.inf _) => .special (.inf false)
  | .special .nan => .special .nan
noncomputable def logb : Num → Num
  | .finite x => if x = 0 then .special (.inf true) else .finite (Int.log 2 |x|)
  | .special (.inf _) => .special (.inf false)
  | .special .nan => .special .nan
noncomputable def exp2 : Num → Num
  | .finite x => .finite ((2 : ℝ) ^ x)
  | .special (.inf false) => .special (.inf false)
  | .special (.inf true) => .finite 0
  | .special .nan => .special .nan
noncomputable def min : Num → Num → Num
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf true), _ | _, .special (.inf true) => .special (.inf true)
  | .special (.inf false), v | v, .special (.inf false) => v
  | .finite x, .finite y => .finite (Min.min x y)
noncomputable def max : Num → Num → Num
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf false), _ | _, .special (.inf false) => .special (.inf false)
  | .special (.inf true), v | v, .special (.inf true) => v
  | .finite x, .finite y => .finite (Max.max x y)
noncomputable def eq : Num → Num → Bool
  | .finite x, .finite y => decide (x = y)
  | .special (.inf a), .special (.inf b) => a == b
  | _, _ => false
noncomputable def lt : Num → Num → Bool
  | .finite x, .finite y => decide (x < y)
  | .special (.inf true), .finite _ | .special (.inf true), .special (.inf false)
  | .finite _, .special (.inf false) => true
  | _, _ => false
noncomputable def le (u v : Num) : Bool := lt u v || eq u v
def isNaN : Num → Bool
  | .special .nan => true
  | _ => false
def isInf : Num → Bool
  | .special (.inf _) => true
  | _ => false
end Num
inductive ArithOp where
  | add | sub | mul | div | sqrt | fma | neg | abs | logb | exp2 | min | max | round | cast
deriving DecidableEq
inductive ExactOp where
  | lt | le | eq | len | isNaN | isInf | and | or | not
deriving DecidableEq
noncomputable def ArithOp.eval : ArithOp → List Num → Option Num
  | .add, [u, v] => some (Num.add u v)
  | .sub, [u, v] => some (Num.sub u v)
  | .mul, [u, v] => some (Num.mul u v)
  | .div, [u, v] => some (Num.div u v)
  | .sqrt, [u] => some (Num.sqrt u)
  | .fma, [u, v, w] => some (Num.fma u v w)
  | .neg, [u] => some (Num.neg u)
  | .abs, [u] => some (Num.abs u)
  | .logb, [u] => some (Num.logb u)
  | .exp2, [u] => some (Num.exp2 u)
  | .min, [u, v] => some (Num.min u v)
  | .max, [u, v] => some (Num.max u v)
  | .round, [u] | .cast, [u] => some u
  | _, _ => none
noncomputable def ExactOp.eval : ExactOp → List Val → Option Val
  | .lt, [.num u, .num v] => some (.bool (Num.lt u v))
  | .le, [.num u, .num v] => some (.bool (Num.le u v))
  | .eq, [.num u, .num v] => some (.bool (Num.eq u v))
  | .len, [.list vs] => some (.num (.finite vs.length))
  | .isNaN, [.num u] => some (.bool (Num.isNaN u))
  | .isInf, [.num u] => some (.bool (Num.isInf u))
  | .and, [.bool a, .bool b] => some (.bool (a && b))
  | .or, [.bool a, .bool b] => some (.bool (a || b))
  | .not, [.bool a] => some (.bool !a)
  | _, _ => none
structure RoundCtx where
  F : FiniteFormat
  S : SpecialMap F.toFormat
  O : OverflowMap F.toFormat
  rm : RoundingMode
  defined : ¬ F.IsUndefined rm
noncomputable def RoundCtx.round (c : RoundCtx) (n : Num) : Num :=
  match rnd c.F c.S c.O c.rm n with
  | .value v => v.toReal
  | .undefined => n
namespace RoundCtx
end RoundCtx
noncomputable def fpy (decode : List (Label × Val) → Option RoundCtx) : Signature where
  ArithOp := ArithOp
  ExactOp := ExactOp
  arith := ArithOp.eval
  exact := ExactOp.eval
  ρ fs := (decode fs).map RoundCtx.round
variable {decode : List (Label × Val) → Option RoundCtx}
abbrev Expr.arithOp (op : ArithOp) (es : List (Expr (fpy decode))) : Expr (fpy decode) :=
  .arith op es
abbrev Expr.exactOp (op : ExactOp) (es : List (Expr (fpy decode))) : Expr (fpy decode) :=
  .exact op es
end Fpy


