-- Prove2me | Definitions.Def_Mpfx_Format_Defs
-- name    : Mpfx_Format_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:20:52.078069+00:00
-- url     : https://prove2.me/theorems/fee717ab-8b48-43ce-8c8d-8cf87868b615
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
set_option autoImplicit true
namespace Mpfx
inductive Special where
  | inf (negative : Bool)
  | nan
deriving DecidableEq, Repr
inductive WithSpecial (α : Type) where
  | finite (a : α)
  | special (s : Special)
deriving DecidableEq, Repr
def Special.neg : Special → Special
  | .inf negative => .inf !negative
  | .nan => .nan
def WithSpecial.neg {α : Type} [Neg α] : WithSpecial α → WithSpecial α
  | .finite a => .finite (-a)
  | .special s => .special s.neg
def WithSpecial.toReal : WithSpecial Dyadic → WithSpecial ℝ
  | .finite d => .finite d
  | .special s => .special s
structure Format where
  p : Prec
  exp : QExp
  b : Bound
  specials : Set Special
namespace Format
def boundOK : Bound → Dyadic → Prop
  | ⊤, _ => True
  | (b : NonNegDyadic), d => |(d : ℚ)| ≤ ((b.val : Dyadic) : ℚ)
def Mem (F : Format) (d : Dyadic) : Prop :=
  Dyadic.precisionAtMost F.p d ∧
  Dyadic.quantumAtLeast F.exp d ∧
  boundOK F.b d
def unbounded (F : Format) : Format := { F with b := ⊤ }
end Format
instance : Membership Dyadic Format := ⟨Format.Mem⟩
def Format.values (F : Format) : Set (WithSpecial Dyadic)
  | .finite d => d ∈ F
  | .special s => s ∈ F.specials
namespace Format
def NegClosed (F : Format) : Prop := ∀ s ∈ F.specials, s.neg ∈ F.specials
def Nontrivial (F : Format) : Prop :=
  ∃ d : Dyadic, d ∈ F ∧ d ≠ 0
def HasPositive (F : Format) (n : ℕ) : Prop :=
  ∃ f : Fin n → Dyadic, StrictMono (fun i => (f i : ℝ)) ∧ ∀ i, f i ∈ F ∧ (0 : ℝ) < f i
def BoundRep (F : Format) : Prop :=
  ∀ bv : NonNegDyadic, F.b = (bv : Bound) →
    bv.val ∈ F.unbounded
end Format
structure FiniteFormat extends Format where
  finite : toFormat.p ≠ ⊤ ∨ toFormat.exp ≠ ⊥
  pos : toFormat.p ≠ 0
instance : Membership Dyadic FiniteFormat := ⟨fun F d => d ∈ F.toFormat⟩
namespace FiniteFormat
noncomputable def canonicalExp (F : FiniteFormat) (x : ℝ) : ℤ :=
  match F.p, F.exp with
  | ⊤, ⊥ => 0  -- unreachable by `F.finite`
  | ⊤, (e : ℤ) => e
  | (p : ℕ), ⊥ =>
      if x = 0 then 0 else Int.log 2 |x| + 1 - (p : ℤ)
  | (p : ℕ), (e : ℤ) =>
      if x = 0 then e
      else max (Int.log 2 |x| + 1 - (p : ℤ)) e
abbrev IsAboveQuantum (F : FiniteFormat) (x : ℝ) : Prop :=
  F.canonicalExp x ≤ Int.log 2 |x|
def unbounded (F : FiniteFormat) : FiniteFormat where
  toFormat := F.toFormat.unbounded
  finite := F.finite
  pos := F.pos
end FiniteFormat
namespace FiniteFormat
noncomputable def numDigits (F : FiniteFormat) (x : ℝ) : ℤ :=
  if x = 0 then 0 else Int.log 2 |x| + 1 - F.canonicalExp x
end FiniteFormat
end Mpfx


