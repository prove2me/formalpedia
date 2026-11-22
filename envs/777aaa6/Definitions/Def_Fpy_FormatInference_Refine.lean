-- Prove2me | Definitions.Def_Fpy_FormatInference_Refine
-- name    : Fpy_FormatInference_Refine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:11:37.549308+00:00
-- url     : https://prove2.me/theorems/4cc6c1bd-4354-4c42-891b-aa807eaf9c71
-- title:
--   Refine
-- statement:
--   Definitions and structural lemmas for Refine, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Refine.lean

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
set_option autoImplicit true
namespace Fpy
open Mpfx
inductive Cmp where
  | lt | le | eq
noncomputable def Cmp.eval : Cmp → Num → Num → Bool
  | .lt => Num.lt
  | .le => Num.le
  | .eq => Num.eq
def Cmp.ofOp : ExactOp → Option Cmp
  | .lt => some .lt
  | .le => some .le
  | .eq => some .eq
  | _ => none
inductive Lhs where
  | id | abs | logb
noncomputable def Lhs.eval : Lhs → Num → Num
  | .id => fun u => u
  | .abs => Num.abs
  | .logb => Num.logb
structure Atom where
  x : Var
  g : Lhs
  cmp : Cmp
  c : Num
  flip : Bool
def Atom.CmpHolds (a : Atom) (v : Num) (b : Bool) : Prop :=
  (if a.flip then a.cmp.eval a.c v else a.cmp.eval v a.c) = b
def Atom.Holds (a : Atom) (u : Num) (b : Bool) : Prop := a.CmpHolds (a.g.eval u) b
variable {decode : List (Label × Val) → Option RoundCtx}
def parseLhs : Option Val → Expr (fpy decode) → Option (Var × Lhs)
  | _, .var x => some (x, .id)
  | some .real, .arith op [.var x] =>
    if (show ArithOp from op) = .abs then some (x, .abs)
    else if (show ArithOp from op) = .logb then some (x, .logb)
    else none
  | _, _ => none
def parseAtom (κ : Option Val) : Expr (fpy decode) → Option Atom
  | .exact op [e, .num c] => do
    let k ← Cmp.ofOp op
    let (x, g) ← parseLhs κ e
    pure ⟨x, g, k, c, false⟩
  | .exact op [.num c, e] => do
    let k ← Cmp.ofOp op
    let (x, g) ← parseLhs κ e
    pure ⟨x, g, k, c, true⟩
  | _ => none
variable {Φ : Program (fpy decode)}
noncomputable def narrowLogb (F : Format) (k : ℤ) : Format :=
  if F.p = ⊤ then F else { F with exp := max F.exp ((k - F.p.toNat + 1 : ℤ) : QExp) }
open Classical in
/-- Narrows `F` to the values passing the test: a test implying `|x| ≤ c`
lowers the bound to `c`, and one implying `logb x ≥ c` raises the minimum
exponent. Other tests leave `F` unchanged. -/
noncomputable def Atom.narrow (a : Atom) (b : Bool) (F : Format) : Format :=
  match a.g, a.c with
  | .abs, .finite r =>
    if h : (∀ y, a.CmpHolds (.finite y) b → y ≤ r) ∧
        ∃ d : NonNegDyadic, ((d.1 : Mpfx.Dyadic) : ℝ) = r then
      { F with b := min F.b ↑(Classical.choose h.2) }
    else F
  | .logb, .finite r =>
    if ¬ a.CmpHolds (.special (.inf true)) b ∧ ∀ y, a.CmpHolds (.finite y) b → r ≤ y then
      narrowLogb F ⌈r⌉
    else F
  | _, _ => F
open Classical in
/-- Narrows a format of Figure 4: a set keeps the values that pass. -/
noncomputable def Atom.narrowFmt (a : Atom) (b : Bool) : Fmt → Fmt
  | .set S => .set (S.filter fun u => a.Holds u b)
  | .abs F => .abs (a.narrow b F)
  | .top => .top
variable {c : Ceiling}
noncomputable def Atom.refine (a : Atom) (b : Bool) (Γ : AEnv (Fmt.domain c)) :
    AEnv (Fmt.domain c) :=
  match Γ a.x with
  | some (.fmt F) => Γ.update a.x (.fmt (a.narrowFmt b F))
  | _ => Γ
noncomputable def refine (κ : Option Val) (e : Expr (fpy decode)) (b : Bool)
    (Γ : AEnv (Fmt.domain c)) : AEnv (Fmt.domain c) :=
  match e with
  | .exact op [e₁] =>
    if (show ExactOp from op) = .not then refine κ e₁ (!b) Γ
    else (parseAtom κ e).elim Γ (·.refine b Γ)
  | .exact op [e₁, e₂] =>
    if (show ExactOp from op) = .and ∧ b = true ∨ (show ExactOp from op) = .or ∧ b = false then
      refine κ e₂ b (refine κ e₁ b Γ)
    else (parseAtom κ e).elim Γ (·.refine b Γ)
  | e => (parseAtom κ e).elim Γ (·.refine b Γ)
end Fpy


