-- Prove2me | Definitions.Def_Fpy_Syntax
-- name    : Fpy_Syntax
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:31:08.024443+00:00
-- url     : https://prove2.me/theorems/960a8acf-cf19-41ab-a51b-eacf2f70b57b
-- title:
--   Syntax
-- statement:
--   Definitions and structural lemmas for Syntax, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Syntax.lean

import Definitions.Def_Fpy_Value
set_option autoImplicit true
namespace Fpy
abbrev Var := String
abbrev Fn := String
structure Signature where
  /-- Operators that round under the current context. -/
  ArithOp : Type
  /-- Operators that never round. -/
  ExactOp : Type
  /-- The exact result `[[op(n₁, …, nₖ)]]` of a rounded operator. -/
  arith : ArithOp → List Num → Option Num
  /-- The result of an unrounded operator. -/
  exact : ExactOp → List Val → Option Val
  /-- The rounding function of the context built from a record; `none` off
  `dom(ρ)`. -/
  ρ : List (Label × Val) → Option (Num → Num)
variable (L : Signature)
inductive Expr where
  | bool (b : Bool)
  | num (n : Num)
  | var (x : Var)
  | arith (op : L.ArithOp) (args : List Expr)
  | exact (op : L.ExactOp) (args : List Expr)
  | list (es : List Expr)
  | index (e₁ e₂ : Expr)
  | record (fs : List (Label × Expr))
  | proj (e : Expr) (l : Label)
  | call (f : Fn) (e : Expr)
  /-- The real context `R`. -/
  | real
  /-- The context constructor `ctx e`. -/
  | ctx (e : Expr)
inductive Stmt where
  | assign (x : Var) (e : Expr L)
  | seq (s₁ s₂ : Stmt)
  | ite (e : Expr L) (s₁ s₂ : Stmt)
  | whileDo (e : Expr L) (s : Stmt)
  | ret (e : Expr L)
  | assert (e : Expr L)
  | skip
  /-- The context statement `with e in s`. -/
  | withCtx (e : Expr L) (s : Stmt)
abbrev Program := Fn → Option (Var × Stmt L)
end Fpy


