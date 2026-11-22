-- Prove2me | Definitions.Def_Mpfx_Rounding_Special
-- name    : Mpfx_Rounding_Special
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:28:33.868177+00:00
-- url     : https://prove2.me/theorems/f5f66b46-f138-45d2-95cc-a5bb528dc3e4
-- title:
--   Special
-- statement:
--   Definitions and structural lemmas for Special, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Special.lean

import Definitions.Def_Mpfx_Rounding_Op
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_neg_mem
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_neg_mem
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_withBound_b
import Theorems.Thm_Mpfx_Format_withBound_exp
import Theorems.Thm_Mpfx_Format_withBound_p
import Theorems.Thm_Mpfx_Format_withBound_specials
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_nonneg
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_boundOK_coe_of_abs_le
import Theorems.Thm_Mpfx_mem_of_mem_unbounded_of_boundOK
import Theorems.Thm_Mpfx_nonneg_coe_real
import Theorems.Thm_Mpfx_not_isUndefined_toNegative
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
import Theorems.Thm_Mpfx_rnd_special
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
attribute [local simp] Mpfx.FiniteFormat.IsEven.neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsOdd.neg_iff
attribute [local simp] Mpfx.FiniteFormat.extend_toFormat
attribute [local simp] Mpfx.FiniteFormat.isEven_zero
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_isUndefined
attribute [local simp] Mpfx.FiniteFormat.unbounded_p
attribute [local simp] Mpfx.FiniteFormat.unbounded_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_unbounded
attribute [local simp] Mpfx.Format.boundAfterNext_top
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Format.withBound_b
attribute [local simp] Mpfx.Format.withBound_exp
attribute [local simp] Mpfx.Format.withBound_p
attribute [local simp] Mpfx.Format.withBound_specials
attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special
attribute [local simp] Mpfx.rnd_special


set_option autoImplicit true
namespace Mpfx
namespace FiniteFormat
noncomputable def maxFinite (F : FiniteFormat) (hb : F.b ≠ ⊤) : Dyadic :=
  rndUnbounded F .toNegative (((F.b.untop hb).val : Dyadic) : ℝ) (not_isUndefined_toNegative F)
theorem maxFinite_spec (F : FiniteFormat) (hb : F.b ≠ ⊤) :
    RoundsFinite F.unbounded .toNegative (((F.b.untop hb).val : Dyadic) : ℝ)
      (F.maxFinite hb) :=
  rndUnbounded_satisfies _ _ _ _
theorem maxFinite_nonneg (F : FiniteFormat) (hb : F.b ≠ ⊤) :
    (0 : ℝ) ≤ (F.maxFinite hb : ℝ) :=
  RoundsFinite.toNegative_nonneg (nonneg_coe_real _) (F.maxFinite_spec hb)
theorem maxFinite_mem (F : FiniteFormat) (hb : F.b ≠ ⊤) : F.maxFinite hb ∈ F := by
  obtain ⟨hmem, hle, -⟩ := F.maxFinite_spec hb
  refine mem_of_mem_unbounded_of_boundOK hmem ?_
  rw [← WithTop.coe_untop F.b hb]
  exact boundOK_coe_of_abs_le (by rw [abs_of_nonneg (F.maxFinite_nonneg hb)]; exact hle)
noncomputable def saturated (F : FiniteFormat) (hb : F.b ≠ ⊤) (negative : Bool) :
    WithSpecial Dyadic :=
  .finite (if negative then -F.maxFinite hb else F.maxFinite hb)
theorem saturated_mem (F : FiniteFormat) (hb : F.b ≠ ⊤) (negative : Bool) :
    F.saturated hb negative ∈ F.values := by
  cases negative
  · exact F.maxFinite_mem hb
  · exact neg_mem (F.maxFinite_mem hb)
end FiniteFormat
namespace SpecialMap
def exact (F : Format) (h : ∀ s, s ∈ F.specials) : SpecialMap F :=
  ⟨.special, h⟩
@[simp] theorem exact_map (F : Format) (h : ∀ s, s ∈ F.specials) (s : Special) :
    (exact F h).map s = .special s := rfl
noncomputable def saturate (F : FiniteFormat) (hb : F.b ≠ ⊤)
    (hnan : Special.nan ∈ F.specials) : SpecialMap F.toFormat where
  map
    | .inf negative => F.saturated hb negative
    | .nan => .special .nan
  mem
    | .inf negative => F.saturated_mem hb negative
    | .nan => hnan
def toNaN (F : Format) (hnan : Special.nan ∈ F.specials) : SpecialMap F :=
  ⟨fun _ => .special .nan, fun _ => hnan⟩
end SpecialMap
namespace OverflowMap
noncomputable def ieee (F : FiniteFormat) (rm : RoundingMode) (hb : F.b ≠ ⊤)
    (hinf : ∀ negative, Special.inf negative ∈ F.specials) : OverflowMap F.toFormat where
  map negative :=
    match rm with
    | .toZero => F.saturated hb negative
    | .toPositive => if negative then F.saturated hb true else .special (.inf false)
    | .toNegative => if negative then .special (.inf true) else F.saturated hb false
    | .awayZero | .toOdd | .nearest _ => .special (.inf negative)
  mem negative := by
    cases rm <;> dsimp only <;> (try split) <;>
      first | exact F.saturated_mem hb _ | exact hinf _
noncomputable def saturate (F : FiniteFormat) (hb : F.b ≠ ⊤) : OverflowMap F.toFormat :=
  ⟨F.saturated hb, F.saturated_mem hb⟩
def toNaN (F : Format) (hnan : Special.nan ∈ F.specials) : OverflowMap F :=
  ⟨fun _ => .special .nan, fun _ => hnan⟩
end OverflowMap
end Mpfx


