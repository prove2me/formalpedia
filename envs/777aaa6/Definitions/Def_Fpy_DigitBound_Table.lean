-- Prove2me | Definitions.Def_Fpy_DigitBound_Table
-- name    : Fpy_DigitBound_Table
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:17:07.510754+00:00
-- url     : https://prove2.me/theorems/18362da5-ac00-49ad-851d-556b41bc17b0
-- title:
--   Table
-- statement:
--   Definitions and structural lemmas for Table, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
namespace Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
def OpOK (op : ArithOp) (Is : List (Term × Term × Option Term)) (n₀ n₁ : ℕ) (Ψ : List Con)
    (l m : Term) : Prop :=
  ∀ ι ns u, List.Forall₂ (fun (I : Term × Term × Option Term) n => NumIn ι I.1 I.2.1 I.2.2 n)
    Is ns → op.eval ns = some u → ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ NumIn ι' l m none u
variable (decode) in
/-- `rnd♮_κ([l, m])`: `[l', m']`, with fresh variables `[n₀, n₁)` bounded by
`Ψ`, bounds the rounding of a value in `[l, m]` under any context `κ` admits. -/
def RndOK (κ : Option SCtx) (l m : Term) (n₀ n₁ : ℕ) (Ψ : List Con) (l' m' : Term) : Prop :=
  ∀ ι u C r, NumIn ι l m none u → (∀ K ∈ κ, K.Admits ι C) → C.rnd (fpy decode) = some r →
    ∃ ι', AgreeOut n₀ n₁ ι ι' ∧ Sat ι' Ψ ∧ NumIn ι' l' m' none (r u)
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}
def ImagesIn (c : RoundCtx) (lo hi : EInt) : Prop :=
  (∀ b, InRange lo hi (c.O.map b).toReal) ∧
    ∀ s, InRange lo hi (c.S.map s).toReal ∨ ∃ a b, s = .inf a ∧ c.S.map s = .special (.inf b)
variable (decode) in
/-- Each context `κ` admits decodes to a context `P` accepts, whose overflow
and special values have digits in `[Lo, Ho]`. -/
def Decodes (κ : Option SCtx) (P : Asgn → RoundCtx → Prop) (Lo Ho : Term) : Prop :=
  ∀ ι C r, (∀ K ∈ κ, K.Admits ι C) → C.rnd (fpy decode) = some r →
    ∃ c : RoundCtx, r = c.round ∧ P ι c ∧ ImagesIn c (Lo.eval ι) (Ho.eval ι)
def QuantumIs (τ : Term) (ι : Asgn) (c : RoundCtx) : Prop := ∃ k : ℤ, τ.eval ι = k ∧ c.F.exp = k
variable {κ : Option SCtx} {Lo Ho : Term}
end Fpy.DigitBound


