-- Prove2me | Definitions.Def_Mpfx_Format_Containment
-- name    : Mpfx_Format_Containment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:37:40.011185+00:00
-- url     : https://prove2.me/theorems/a550a89d-6a09-483e-ba74-af48eae68e4c
-- title:
--   Containment
-- statement:
--   Definitions and structural lemmas for Containment, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean

import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_p_pos
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
attribute [local simp] Mpfx.Dyadic.coe_abs
attribute [local simp] Mpfx.Dyadic.coe_half
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_rat_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_half
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_mul
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_sub
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.Dyadic.precisionAtMost_neg_iff
attribute [local simp] Mpfx.Dyadic.precisionAtMost_top
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_bot
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_neg_iff
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_p
attribute [local simp] Mpfx.FiniteFormat.unbounded_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_unbounded
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special


set_option autoImplicit true
namespace Mpfx
namespace Format
structure Subset (F₁ F₂ : Format) : Prop where
  mem : ∀ x : Dyadic, x ∈ F₁ → x ∈ F₂
  specials : F₁.specials ⊆ F₂.specials
instance : HasSubset Format := ⟨Subset⟩
instance {F₁ F₂ : Format} : CoeFun (F₁ ⊆ F₂) (fun _ => ∀ x : Dyadic, x ∈ F₁ → x ∈ F₂) :=
  ⟨Subset.mem⟩
theorem Subset.refl (F : Format) : F ⊆ F := ⟨fun _ h => h, subset_rfl⟩
theorem Subset.trans {F₁ F₂ F₃ : Format} (h₁ : F₁ ⊆ F₂) (h₂ : F₂ ⊆ F₃) : F₁ ⊆ F₃ :=
  ⟨fun x hx => h₂.mem x (h₁.mem x hx), h₁.specials.trans h₂.specials⟩
instance : Std.Refl (α := Format) (· ⊆ ·) := ⟨Subset.refl⟩
instance : IsTrans Format (· ⊆ ·) := ⟨fun _ _ _ => Subset.trans⟩
def nnPow (e : ℤ) : NonNegDyadic :=
  ⟨Dyadic.ofIntZpow 1 e, by rw [Dyadic.coe_rat_ofIntZpow]; positivity⟩
@[simp] theorem coe_nnPow (e : ℤ) : ((nnPow e).val : ℚ) = (2 : ℚ) ^ e := by
  change ((Dyadic.ofIntZpow 1 e : Dyadic) : ℚ) = _
  rw [Dyadic.coe_rat_ofIntZpow]; push_cast; ring
@[simp] theorem coe_real_nnPow (e : ℤ) : (((nnPow e).val : Dyadic) : ℝ) = (2 : ℝ) ^ e := by
  rw [Dyadic.coe_real_eq_ratCast, coe_nnPow]; push_cast; ring
def wit (p : ℕ) : ℤ := 2 ^ p + 1
def ContainsPrec (F₁ F₂ : Format) : Prop :=
  F₁.p ≤ F₂.p ∧ F₂.exp ≤ F₁.exp ∧ F₁.b ≤ F₂.b ∧ F₁.specials ⊆ F₂.specials
def ContainsSub (F₁ F₂ : Format) : Prop :=
  ∃ (e₁ : ℤ) (p₂ : ℕ), F₁.exp = (e₁ : QExp) ∧ 0 < p₂ ∧ F₂.p = (p₂ : Prec) ∧
    F₁.b ≤ ((nnPow (e₁ + (p₂ : ℤ)) : NonNegDyadic) : Bound) ∧
    F₂.exp ≤ F₁.exp ∧ F₁.b ≤ F₂.b ∧ F₁.specials ⊆ F₂.specials
def extend (F : Format) (k : ℕ) : Format where
  p := F.p + k
  exp := F.exp.map (· - (k : ℤ))
  b := F.b
  specials := F.specials
@[simp] theorem extend_b (F : Format) k : (F.extend k).b = F.b := rfl
@[simp] theorem extend_specials (F : Format) k : (F.extend k).specials = F.specials := rfl
@[simp] theorem extend_p (F : Format) (k : ℕ) : (F.extend k).p = F.p + k := rfl
end Format
namespace FiniteFormat
def extend (F : FiniteFormat) (k : ℕ) : FiniteFormat where
  toFormat := F.toFormat.extend k
  finite := by
    rcases F.finite with hp | he
    · left
      change F.p + (k : Prec) ≠ ⊤
      exact fun h => hp (WithTop.add_eq_top.mp h |>.resolve_right (ENat.coe_ne_top k))
    · right
      change F.exp.map (· - (k : ℤ)) ≠ ⊥
      cases hF : F.exp using QExp.recBotCoe with
      | bot => exact absurd hF he
      | coe e => rw [WithBot.map_coe]; exact WithBot.coe_ne_bot
  pos := by
    change F.p + (k : Prec) ≠ 0
    exact fun h => F.pos (by simpa using (add_eq_zero.mp h).1)
end FiniteFormat
namespace Format
def shrink (F : Format) : Format := { F with p := F.p - 1, exp := F.exp.map (· + 1) }
end Format
namespace FiniteFormat
def shrink (F : FiniteFormat) (h : F.p ≠ ((1 : ℕ) : Prec)) : FiniteFormat where
  toFormat := F.toFormat.shrink
  finite := by
    rcases F.finite with hp | he
    · left
      change F.p - 1 ≠ ⊤
      cases hF : F.p using ENat.recTopCoe with
      | top => exact absurd hF hp
      | coe n => exact_mod_cast ENat.coe_ne_top (n - 1)
    · right
      change F.exp.map (· + 1) ≠ ⊥
      cases hF : F.exp using QExp.recBotCoe with
      | bot => exact absurd hF he
      | coe e => exact WithBot.coe_ne_bot
  pos := by
    change F.p - 1 ≠ 0
    cases hF : F.p using ENat.recTopCoe with
    | top => exact (show (⊤ : Prec) - 1 = ⊤ from rfl) ▸ ENat.top_ne_zero
    | coe n =>
      have h0 := F.p_pos hF
      have h1 : n ≠ 1 := fun h1 => h (by rw [hF, h1])
      change (n : Prec) - ((1 : ℕ) : Prec) ≠ ((0 : ℕ) : Prec)
      rw [← ENat.coe_sub]
      exact fun hzero => (show n - 1 ≠ 0 by omega) (ENat.coe_inj.mp hzero)
end FiniteFormat
namespace Format
end Format
end Mpfx


