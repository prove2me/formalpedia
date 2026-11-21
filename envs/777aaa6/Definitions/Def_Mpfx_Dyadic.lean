-- Prove2me | Definitions.Def_Mpfx_Dyadic
-- name    : Mpfx_Dyadic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:19:19.830529+00:00
-- url     : https://prove2.me/theorems/f77a129c-c229-41aa-8b2c-5aa49d15f257
-- title:
--   Dyadic
-- statement:
--   Definitions and structural lemmas for Dyadic, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Theorems.Thm_Mpfx_two_zpow_split_toNat

set_option autoImplicit true
namespace Mpfx
abbrev Prec := ℕ∞
@[simp] theorem Prec.some_eq_coe p : (WithTop.some p : Prec) = (p : Prec) := rfl
abbrev QExp := WithBot ℤ
@[elab_as_elim] def QExp.recBotCoe {C : QExp → Sort*} (bot : C ⊥)
    (coe : ∀ e : ℤ, C (e : QExp)) : ∀ e : QExp, C e
  | ⊥ => bot
  | (e : ℤ) => coe e
def IsDyadic (x : ℚ) : Prop := ∃ c e : ℤ, x = (c : ℚ) * (2 : ℚ) ^ e
namespace IsDyadic
theorem add_aux (c₁ c₂ e₁ e₂ : ℤ) (h : e₁ ≤ e₂) :
    (c₁ : ℚ) * (2 : ℚ) ^ e₁ + (c₂ : ℚ) * (2 : ℚ) ^ e₂
      = ((c₁ + c₂ * 2 ^ (e₂ - e₁).toNat : ℤ) : ℚ) * (2 : ℚ) ^ e₁ := by
  rw [Mpfx.two_zpow_split_toNat (K := ℚ) h]; push_cast; ring
theorem zero : IsDyadic 0 := ⟨0, 0, by simp⟩
theorem one : IsDyadic 1 := ⟨1, 0, by simp⟩
theorem neg {x : ℚ} (h : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨c, e, rfl⟩ := h
  exact ⟨-c, e, by push_cast; ring⟩
theorem mul {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x * y) := by
  obtain ⟨c₁, e₁, rfl⟩ := hx
  obtain ⟨c₂, e₂, rfl⟩ := hy
  refine ⟨c₁ * c₂, e₁ + e₂, ?_⟩
  rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  push_cast; ring
theorem add {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨c₁, e₁, rfl⟩ := hx
  obtain ⟨c₂, e₂, rfl⟩ := hy
  rcases le_total e₁ e₂ with h | h
  · exact ⟨c₁ + c₂ * 2 ^ (e₂ - e₁).toNat, e₁, add_aux c₁ c₂ e₁ e₂ h⟩
  · refine ⟨c₂ + c₁ * 2 ^ (e₁ - e₂).toNat, e₂, ?_⟩
    rw [add_comm]
    exact add_aux c₂ c₁ e₂ e₁ h
end IsDyadic
def dyadicSubring : Subring ℚ where
  carrier := { x | IsDyadic x }
  zero_mem' := IsDyadic.zero
  one_mem' := IsDyadic.one
  add_mem' := IsDyadic.add
  neg_mem' := IsDyadic.neg
  mul_mem' := IsDyadic.mul
abbrev Dyadic : Type := dyadicSubring
namespace Dyadic
def abs (x : Dyadic) : Dyadic :=
  if 0 ≤ (x : ℚ) then x else -x
def ofIntZpow (c e : ℤ) : Dyadic :=
  ⟨(c : ℚ) * (2 : ℚ) ^ e, c, e, rfl⟩
def half : Dyadic := ofIntZpow 1 (-1)
def midpoint (y₁ y₂ : Dyadic) : Dyadic := (y₁ + y₂) * half
def precisionAtMost : Prec → Dyadic → Prop
  | ⊤, _ => True
  | (p : ℕ), x => ∃ c e : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧ |c| < (2 : ℤ) ^ p
def quantumAtLeast : QExp → Dyadic → Prop
  | ⊥, _ => True
  | (e : ℤ), x => ∃ c : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e
def IsRepresentableAtP (p : ℕ) (c e : ℤ) (y : Dyadic) : Prop :=
  (y : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧
  (2 : ℤ) ^ (p - 1) ≤ |c| ∧ |c| < (2 : ℤ) ^ p
instance : DecidableEq Dyadic := Subtype.instDecidableEq
end Dyadic
abbrev NonNegDyadic : Type := { d : Dyadic // 0 ≤ (d : ℚ) }
abbrev Bound := WithTop NonNegDyadic
@[elab_as_elim] def Bound.recTopCoe {C : Bound → Sort*} (top : C ⊤)
    (coe : ∀ b : NonNegDyadic, C (b : Bound)) : ∀ b : Bound, C b
  | ⊤ => top
  | (b : NonNegDyadic) => coe b
namespace Dyadic
end Dyadic
end Mpfx


