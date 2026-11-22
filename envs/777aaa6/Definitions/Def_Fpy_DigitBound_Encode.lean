-- Prove2me | Definitions.Def_Fpy_DigitBound_Encode
-- name    : Fpy_DigitBound_Encode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:43:15.205384+00:00
-- url     : https://prove2.me/theorems/24b66b10-0cd1-4db5-9e1f-75dfdcded4e1
-- title:
--   Encode
-- statement:
--   Definitions and structural lemmas for Encode, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean

import Definitions.Def_Fpy_DigitBound_Sound
import Theorems.Thm_Fpy_DigitBound_LsbAt_le
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg

set_option autoImplicit true
namespace Fpy.DigitBound
open Mpfx
mutual

/-- Integer terms; `max` and `min` are `ite`. -/
inductive ITerm where
  | const (k : ℤ)
  | var (x : ℕ)
  | add (a b : ITerm)
  | smul (c : ℤ) (a : ITerm)
  | ite (φ : IForm) (a b : ITerm)

/-- Formulas over integer terms and the flags. -/
inductive IForm where
  | tt
  | ff
  | notTop (x : ℕ)
  | notBot (x : ℕ)
  | le (a b : ITerm)
  | not (φ : IForm)
  | and (φ ψ : IForm)
  | or (φ ψ : IForm)

end
structure IModel where
  val : ℕ → ℤ
  notTop : ℕ → Bool
  notBot : ℕ → Bool
mutual

def ITerm.eval (M : IModel) : ITerm → ℤ
  | .const k => k
  | .var x => M.val x
  | .add a b => a.eval M + b.eval M
  | .smul c a => c * a.eval M
  | .ite φ a b => if φ.holds M then a.eval M else b.eval M

def IForm.holds (M : IModel) : IForm → Bool
  | .tt => true
  | .ff => false
  | .notTop x => M.notTop x
  | .notBot x => M.notBot x
  | .le a b => decide (a.eval M ≤ b.eval M)
  | .not φ => !φ.holds M
  | .and φ ψ => φ.holds M && ψ.holds M
  | .or φ ψ => φ.holds M || ψ.holds M

end
def decodeE (T B : Bool) (k : ℤ) : EInt := if T then ⊤ else if B then ⊥ else k
def IModel.decode (M : IModel) : Asgn := fun x => decodeE (!M.notTop x) (!M.notBot x) (M.val x)
def IModel.ofAsgn (ι : Asgn) : IModel where
  val x := WithBotTop.rec (motive := fun _ => ℤ) 0 id 0 (ι x)
  notTop x := ι x ≠ ⊤
  notBot x := ι x ≠ ⊥
structure EncTerm where
  top : IForm
  bot : IForm
  val : ITerm
def Term.enc : Term → EncTerm
  | .const z => WithBotTop.rec (motive := fun _ => EncTerm) ⟨.ff, .tt, .const 0⟩
      (fun k => ⟨.ff, .ff, .const k⟩) ⟨.tt, .ff, .const 0⟩ z
  | .var x => ⟨.not (.notTop x), .and (.notTop x) (.not (.notBot x)), .var x⟩
  | .add a b => ⟨.and (.not (.or a.enc.bot b.enc.bot)) (.or a.enc.top b.enc.top),
      .or a.enc.bot b.enc.bot, .add a.enc.val b.enc.val⟩
  | .neg a => ⟨a.enc.bot, a.enc.top, .smul (-1) a.enc.val⟩
  | .smul c a => if 0 < c then ⟨a.enc.top, a.enc.bot, .smul c a.enc.val⟩
      else if c < 0 then ⟨a.enc.bot, a.enc.top, .smul c a.enc.val⟩
      else ⟨.ff, .ff, .const 0⟩
  | .max a b => ⟨.or a.enc.top b.enc.top, .and a.enc.bot b.enc.bot,
      .ite a.enc.bot b.enc.val (.ite b.enc.bot a.enc.val
        (.ite (.le a.enc.val b.enc.val) b.enc.val a.enc.val))⟩
  | .min a b => ⟨.and a.enc.top b.enc.top, .or a.enc.bot b.enc.bot,
      .ite a.enc.top b.enc.val (.ite b.enc.top a.enc.val
        (.ite (.le a.enc.val b.enc.val) a.enc.val b.enc.val))⟩
def Atom.enc (a : Atom) : IForm :=
  .or a.lhs.enc.bot (.or a.rhs.enc.top
    (.and (.not a.lhs.enc.top) (.and (.not a.rhs.enc.bot) (.le a.lhs.enc.val a.rhs.enc.val))))
def encode (Ψ : List Con) : List IForm := Ψ.flatMap fun c => c.atoms.map Atom.enc
end Fpy.DigitBound


