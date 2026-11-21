-- Prove2me | Definitions.Def_Mpfx_Format_Next
-- name    : Mpfx_Format_Next
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:38:42.537858+00:00
-- url     : https://prove2.me/theorems/6b901c37-d17c-460f-b3a8-42988a895207
-- title:
--   Next
-- statement:
--   Definitions and structural lemmas for Next, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean

import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_add


set_option autoImplicit true
namespace Mpfx
namespace Format
def withBound (F : Format) (b' : Bound) : Format := { F with b := b' }
noncomputable def next (F : Format) (b : _root_.Mpfx.Dyadic) : _root_.Mpfx.Dyadic :=
  match F.exp, F.p with
  | (e : ℤ), (p : ℕ) =>
    if (b : ℝ) ≤ 0 then
      _root_.Mpfx.Dyadic.ofIntZpow 1 e
    else
      let logB : ℤ := Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ)
      let stepExp : ℤ := max e (logB - (p : ℤ) + 1)
      b + _root_.Mpfx.Dyadic.ofIntZpow 1 stepExp
  | (e : ℤ), ⊤ => b + _root_.Mpfx.Dyadic.ofIntZpow 1 e
  | ⊥, (p : ℕ) =>
    if (b : ℝ) ≤ 0 then
      b + 1
    else
      b + _root_.Mpfx.Dyadic.ofIntZpow 1 (Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) - (p : ℤ) + 1)
  | ⊥, ⊤ => b + 1
theorem lt_next_of_finite (F : Format) {e : ℤ} {p : ℕ}
    (he : F.exp = (e : QExp)) (hp : F.p = (p : Prec)) (b : _root_.Mpfx.Dyadic)
    (hb : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    (b : ℝ) < (F.next b : ℝ) := by
  have h_ulp_pos : ∀ k : ℤ, (0 : ℝ) < ((_root_.Mpfx.Dyadic.ofIntZpow 1 k : _root_.Mpfx.Dyadic) : ℝ) := by
    intro k
    rw [_root_.Mpfx.Dyadic.coe_ofIntZpow]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
    push_cast
    linarith
  have h_next_eq : F.next b =
      if ((b : _root_.Mpfx.Dyadic) : ℝ) ≤ 0 then _root_.Mpfx.Dyadic.ofIntZpow 1 e
      else b + _root_.Mpfx.Dyadic.ofIntZpow 1 (max e (Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) - (p : ℤ) + 1)) := by
    unfold next; rw [he, hp]
  rw [h_next_eq]
  by_cases h : ((b : _root_.Mpfx.Dyadic) : ℝ) ≤ 0
  · rw [if_pos h]
    have hb_zero : ((b : _root_.Mpfx.Dyadic) : ℝ) = 0 := le_antisymm h hb
    rw [hb_zero]
    exact h_ulp_pos e
  · rw [if_neg h]
    push_cast
    have := h_ulp_pos (max e (Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) - (p : ℤ) + 1))
    linarith
theorem lt_next_of_p_top (F : Format) {e : ℤ}
    (he : F.exp = (e : QExp)) (hp : F.p = ⊤) (b : _root_.Mpfx.Dyadic) :
    (b : ℝ) < (F.next b : ℝ) := by
  have h_ulp_pos : (0 : ℝ) < ((_root_.Mpfx.Dyadic.ofIntZpow 1 e : _root_.Mpfx.Dyadic) : ℝ) := by
    rw [_root_.Mpfx.Dyadic.coe_ofIntZpow]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
    push_cast; linarith
  have h_next_eq : F.next b = b + _root_.Mpfx.Dyadic.ofIntZpow 1 e := by
    -- `⊤ : Prec` is not syntactically `Option.none`, so the `match` on
    -- `(F.exp, F.p)` needs an explicit `rfl` to reduce.
    unfold next
    rw [he, hp]
  rw [h_next_eq]; push_cast; linarith
theorem next_eq_bot_p_top' (F : Format) (he : F.exp = ⊥) (hp : F.p = ⊤)
    (b : _root_.Mpfx.Dyadic) : F.next b = b + 1 := by
  unfold next
  rw [he, hp]
theorem next_eq_bot_nonpos (F : Format) (he : F.exp = ⊥) {b : _root_.Mpfx.Dyadic}
    (hb : ((b : _root_.Mpfx.Dyadic) : ℝ) ≤ 0) : F.next b = b + 1 := by
  cases hp : F.p using ENat.recTopCoe with
  | top => exact next_eq_bot_p_top' F he hp b
  | coe p =>
    have h_eq : F.next b =
        if ((b : _root_.Mpfx.Dyadic) : ℝ) ≤ 0 then b + 1
        else b + _root_.Mpfx.Dyadic.ofIntZpow 1
          (Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) - (p : ℤ) + 1) := by
      unfold next; rw [he, hp]
    rw [h_eq, if_pos hb]
theorem next_eq_bot_pos (F : Format) {p : ℕ} (he : F.exp = ⊥)
    (hp : F.p = (p : Prec)) {b : _root_.Mpfx.Dyadic}
    (hb_pos : 0 < ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    F.next b
      = b + _root_.Mpfx.Dyadic.ofIntZpow 1 (Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) - (p : ℤ) + 1) := by
  have h_eq : F.next b =
      if ((b : _root_.Mpfx.Dyadic) : ℝ) ≤ 0 then b + 1
      else b + _root_.Mpfx.Dyadic.ofIntZpow 1
        (Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) - (p : ℤ) + 1) := by
    unfold next; rw [he, hp]
  rw [h_eq, if_neg (not_le.mpr hb_pos)]
theorem lt_next_of_bot (F : Format) (he : F.exp = ⊥) (b : _root_.Mpfx.Dyadic) :
    ((b : _root_.Mpfx.Dyadic) : ℝ) < ((F.next b : _root_.Mpfx.Dyadic) : ℝ) := by
  cases hp : F.p using ENat.recTopCoe with
  | top =>
    rw [next_eq_bot_p_top' F he hp b]
    push_cast
    linarith
  | coe p =>
    by_cases hb0 : ((b : _root_.Mpfx.Dyadic) : ℝ) ≤ 0
    · rw [next_eq_bot_nonpos F he hb0]
      push_cast
      linarith
    · push Not at hb0
      rw [next_eq_bot_pos F he hp hb0, _root_.Mpfx.Dyadic.coe_real_add, _root_.Mpfx.Dyadic.coe_ofIntZpow]
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (Int.log 2 ((b : _root_.Mpfx.Dyadic) : ℝ) - (p : ℤ) + 1) :=
        zpow_pos (by norm_num) _
      push_cast
      linarith
theorem lt_next {F : Format} (b : _root_.Mpfx.Dyadic) (hb : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    ((b : _root_.Mpfx.Dyadic) : ℝ) < ((F.next b : _root_.Mpfx.Dyadic) : ℝ) := by
  cases he : F.exp using QExp.recBotCoe with
  | bot => exact lt_next_of_bot F he b
  | coe e =>
    rcases hp : F.p with _ | p
    · exact lt_next_of_p_top F he hp b
    · exact lt_next_of_finite F he hp b hb
theorem self_le_next (F : Format) (b : _root_.Mpfx.Dyadic)
    (hb : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    ((b : _root_.Mpfx.Dyadic) : ℝ) ≤ ((F.next b : _root_.Mpfx.Dyadic) : ℝ) :=
  (lt_next (F := F) b hb).le
theorem next_nonneg (F : Format) (b : _root_.Mpfx.Dyadic) (hb : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    0 ≤ ((F.next b : _root_.Mpfx.Dyadic) : ℝ) :=
  hb.trans (self_le_next F b hb)
noncomputable def boundAfterNext (F : Format) : Bound :=
  match F.b with
  | ⊤ => ⊤
  | (b : NonNegDyadic) =>
    (⟨F.next b.val, by
        have hb : 0 ≤ ((b.val : _root_.Mpfx.Dyadic) : ℝ) := by
          exact_mod_cast b.2
        have h_next_nn : 0 ≤ ((F.next b.val : _root_.Mpfx.Dyadic) : ℝ) := next_nonneg F b.val hb
        exact_mod_cast h_next_nn⟩ : NonNegDyadic)
end Format
namespace FiniteFormat
noncomputable def next (F : FiniteFormat) (b : _root_.Mpfx.Dyadic) : _root_.Mpfx.Dyadic :=
  if ((b : _root_.Mpfx.Dyadic) : ℝ) = 0 ∧ F.exp = ⊥ then b
  else b + _root_.Mpfx.Dyadic.ofIntZpow 1 (F.canonicalExp ((b : _root_.Mpfx.Dyadic) : ℝ))
end FiniteFormat
def FiniteFormat.withBoundFF (F : FiniteFormat) (B : Bound) :
    FiniteFormat :=
  ⟨F.toFormat.withBound B, F.finite, F.pos⟩
end Mpfx


