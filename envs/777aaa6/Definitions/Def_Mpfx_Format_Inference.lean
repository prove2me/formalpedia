-- Prove2me | Definitions.Def_Mpfx_Format_Inference
-- name    : Mpfx_Format_Inference
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:23:02.977819+00:00
-- url     : https://prove2.me/theorems/25b41c94-81e8-448f-9a8e-7dcc9d566fb4
-- title:
--   Inference
-- statement:
--   Definitions and structural lemmas for Inference, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
set_option autoImplicit true
namespace Mpfx
namespace Format
open scoped Pointwise
def toSet (F : Format) : Set Dyadic := {x | x ∈ F}
end Format
namespace WithSpecial
def mul : WithSpecial Dyadic → WithSpecial Dyadic → WithSpecial Dyadic
  | .finite x, .finite y => .finite (x * y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf a), .special (.inf b) => .special (.inf (xor a b))
  | .special (.inf a), .finite y | .finite y, .special (.inf a) =>
      if y = 0 then .special .nan else .special (.inf (xor a (decide ((y : ℚ) < 0))))
def add : WithSpecial Dyadic → WithSpecial Dyadic → WithSpecial Dyadic
  | .finite x, .finite y => .finite (x + y)
  | .special .nan, _ | _, .special .nan => .special .nan
  | .special (.inf a), .special (.inf b) => if a = b then .special (.inf a) else .special .nan
  | .special (.inf a), .finite _ | .finite _, .special (.inf a) => .special (.inf a)
def abs : WithSpecial Dyadic → WithSpecial Dyadic
  | .finite x => .finite (Dyadic.abs x)
  | .special (.inf _) => .special (.inf false)
  | .special .nan => .special .nan
instance : Mul (WithSpecial Dyadic) := ⟨mul⟩
instance : Add (WithSpecial Dyadic) := ⟨add⟩
instance {α : Type} [Neg α] : Neg (WithSpecial α) := ⟨WithSpecial.neg⟩
end WithSpecial
namespace Format
open scoped Pointwise
def mulSpecials (F₁ F₂ : Format) : Set Special
  | .nan => .nan ∈ F₁.specials ∨ .nan ∈ F₂.specials ∨
      (∃ a, .inf a ∈ F₁.specials) ∨ (∃ b, .inf b ∈ F₂.specials)
  | .inf s => ∃ a b, xor a b = s ∧
      (.inf a ∈ F₁.specials ∧ (.inf b ∈ F₂.specials ∨ F₂.Nontrivial) ∨
        F₁.Nontrivial ∧ .inf b ∈ F₂.specials)
def addSpecials (F₁ F₂ : Format) : Set Special
  | .nan => .nan ∈ F₁.specials ∨ .nan ∈ F₂.specials ∨
      ∃ a, .inf a ∈ F₁.specials ∧ .inf (!a) ∈ F₂.specials
  | .inf s => .inf s ∈ F₁.specials ∨ .inf s ∈ F₂.specials
def absSpecials (F : Format) : Set Special
  | .nan => .nan ∈ F.specials
  | .inf s => s = false ∧ ∃ a, .inf a ∈ F.specials
def opMul (F₁ F₂ : Format) : Format where
  p := F₁.p + F₂.p
  exp := F₁.exp + F₂.exp
  b := match F₁.b, F₂.b with
    | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) =>
        ((⟨b₁.1 * b₂.1, by
            have := mul_nonneg b₁.2 b₂.2
            push_cast at this ⊢
            exact this⟩ : NonNegDyadic) : Bound)
    | _, _ => ⊤
  specials := mulSpecials F₁ F₂
noncomputable def bitsFor (B : ℝ) (m : ℤ) : ℕ := Nat.clog 2 (Int.toNat ⌊B / (2 : ℝ) ^ m⌋ + 1)
noncomputable def opAddPrec (F₁ F₂ : Format) : Prec :=
  match (F₁.b : Bound), (F₂.b : Bound),
        (min F₁.exp F₂.exp : QExp) with
  | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic), (m : ℤ) =>
      (bitsFor ((b₁.1 + b₂.1 : Dyadic) : ℝ) m : Prec)
  | _, _, _ => ⊤
noncomputable def opAdd (F₁ F₂ : Format) : Format where
  p := opAddPrec F₁ F₂
  exp := min F₁.exp F₂.exp
  b := match F₁.b, F₂.b with
    | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) =>
        ((⟨b₁.1 + b₂.1, by
            have := add_nonneg b₁.2 b₂.2
            push_cast at this ⊢
            exact this⟩ : NonNegDyadic) : Bound)
    | _, _ => ⊤
  specials := addSpecials F₁ F₂
def opNeg (F : Format) : Format := { F with specials := {s | s.neg ∈ F.specials} }
def opAbs (F : Format) : Format := { F with specials := absSpecials F }
end Format
end Mpfx


