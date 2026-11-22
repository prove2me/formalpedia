-- Prove2me | Definitions.Def_Fpy_FormatInference_Ops
-- name    : Fpy_FormatInference_Ops
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:10:39.842751+00:00
-- url     : https://prove2.me/theorems/be1ea90b-6fe2-452d-adfb-e752895dbb3f
-- title:
--   Ops
-- statement:
--   Definitions and structural lemmas for Ops, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
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
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
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
import Theorems.Thm_Mpfx_Format_mem_toSet
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
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_add_nan
import Theorems.Thm_Mpfx_WithSpecial_finite_add_finite
import Theorems.Thm_Mpfx_WithSpecial_finite_add_inf
import Theorems.Thm_Mpfx_WithSpecial_finite_mul_finite
import Theorems.Thm_Mpfx_WithSpecial_finite_mul_inf
import Theorems.Thm_Mpfx_WithSpecial_inf_add_finite
import Theorems.Thm_Mpfx_WithSpecial_inf_add_inf
import Theorems.Thm_Mpfx_WithSpecial_inf_mul_finite
import Theorems.Thm_Mpfx_WithSpecial_inf_mul_inf
import Theorems.Thm_Mpfx_WithSpecial_mul_nan
import Theorems.Thm_Mpfx_WithSpecial_nan_add
import Theorems.Thm_Mpfx_WithSpecial_nan_mul
import Theorems.Thm_Mpfx_WithSpecial_neg_def
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
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
attribute [local simp] Mpfx.Format.mem_toSet
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
attribute [local simp] Mpfx.WithSpecial.add_nan
attribute [local simp] Mpfx.WithSpecial.finite_add_finite
attribute [local simp] Mpfx.WithSpecial.finite_add_inf
attribute [local simp] Mpfx.WithSpecial.finite_mul_finite
attribute [local simp] Mpfx.WithSpecial.finite_mul_inf
attribute [local simp] Mpfx.WithSpecial.inf_add_finite
attribute [local simp] Mpfx.WithSpecial.inf_add_inf
attribute [local simp] Mpfx.WithSpecial.inf_mul_finite
attribute [local simp] Mpfx.WithSpecial.inf_mul_inf
attribute [local simp] Mpfx.WithSpecial.mul_nan
attribute [local simp] Mpfx.WithSpecial.nan_add
attribute [local simp] Mpfx.WithSpecial.nan_mul
attribute [local simp] Mpfx.WithSpecial.neg_def
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special
attribute [local simp] Mpfx.rnd_special


set_option autoImplicit true
namespace Fpy
open Mpfx
def _root_.Mpfx.Format.withP (F : Format) (p : Prec) : Format := { F with p := p }
noncomputable def _root_.Mpfx.Format.bits (F : Format) : Prec :=
  match F.b, F.exp with
  | (b : NonNegDyadic), (e : ℤ) => (Format.bitsFor ((b.1 : Mpfx.Dyadic) : ℝ) e : Prec)
  | _, _ => ⊤
noncomputable def _root_.Mpfx.Format.pHat (F : Format) : Prec := min F.p F.bits
noncomputable def precMul (q₁ q₂ : Prec) : Prec :=
  if q₁ = ((1 : ℕ) : Prec) ∨ q₂ = ((1 : ℕ) : Prec) then max q₁ q₂ else max 1 (q₁ + q₂)
noncomputable def addFmt (F₁ F₂ : Format) : Format :=
  (Format.opAdd F₁ F₂).withP (max 1 (Format.opAdd F₁ F₂).p)
noncomputable def mulFmt (F₁ F₂ : Format) : Format :=
  (Format.opMul F₁ F₂).withP (precMul F₁.pHat F₂.pHat)
def logbSpecials (F : Format) : Set Special
  | .inf true => True
  | .inf false => ∃ a, .inf a ∈ F.specials
  | .nan => .nan ∈ F.specials
noncomputable def logbFmt (F : Format) : Fmt :=
  match F.exp, F.b with
  | (e : ℤ), (b : NonNegDyadic) =>
    if 0 < ((b.1 : Mpfx.Dyadic) : ℚ) then
      let b' : ℕ := max e.natAbs (Int.log 2 ((b.1 : Mpfx.Dyadic) : ℝ)).natAbs
      .abs
        { p := max 1 (Format.bitsFor b' 0 : Prec)
          exp := (0 : ℤ)
          b := (⟨Dyadic.ofIntZpow b' 0, by simp⟩ : NonNegDyadic)
          specials := logbSpecials F }
    else .top
  | _, _ => .top
def exp2Specials (F : Format) : Set Special
  | .inf true => False
  | .inf false => .inf false ∈ F.specials
  | .nan => .nan ∈ F.specials
noncomputable def exp2Fmt (F : Format) : Fmt :=
  match F.exp, F.b with
  | (e : ℤ), (b : NonNegDyadic) =>
    if 0 ≤ e then
      .abs
        { p := (1 : ℕ)
          exp := (-⌊((b.1 : Mpfx.Dyadic) : ℚ)⌋ : ℤ)
          b := (⟨Dyadic.ofIntZpow 1 ⌊((b.1 : Mpfx.Dyadic) : ℚ)⌋, by
            rw [Dyadic.coe_rat_ofIntZpow]; positivity⟩ : NonNegDyadic)
          specials := exp2Specials F }
    else .top
  | _, _ => .top
section Lift
variable (c : Ceiling)
open Classical in
/-- A binary row: element-wise on two sets, the row `fa` on abstract formats,
`⌈S⌉` for a set meeting an abstract format, and `R*` otherwise. -/
noncomputable def lift2 (f : Num → Num → Num) (fa : Format → Format → Fmt) : Fmt → Fmt → Fmt
  | .set S₁, .set S₂ => .set (Finset.image₂ f S₁ S₂)
  | .set S, .abs F => (c.ceil S).elim .top (fa · F)
  | .abs F, .set S => (c.ceil S).elim .top (fa F ·)
  | .abs F₁, .abs F₂ => fa F₁ F₂
  | _, _ => .top
open Classical in
/-- A unary row that acts element-wise on a set. -/
noncomputable def lift1 (f : Num → Num) (fa : Format → Fmt) : Fmt → Fmt
  | .set S => .set (S.image f)
  | .abs F => fa F
  | .top => .top
noncomputable def liftCeil (fa : Format → Fmt) : Fmt → Fmt
  | .set S => (c.ceil S).elim .top fa
  | .abs F => fa F
  | .top => .top
variable {c}
end Lift
noncomputable def ArithOp.fmt (c : Ceiling) : ArithOp → List Fmt → Fmt
  | .add, [F₁, F₂] => lift2 c Num.add (fun F₁ F₂ => .abs (addFmt F₁ F₂)) F₁ F₂
  | .sub, [F₁, F₂] =>
      lift2 c Num.sub (fun F₁ F₂ => .abs (addFmt F₁ (Format.opNeg F₂))) F₁ F₂
  | .mul, [F₁, F₂] => lift2 c Num.mul (fun F₁ F₂ => .abs (mulFmt F₁ F₂)) F₁ F₂
  | .neg, [F] => lift1 Num.neg (fun F => .abs (Format.opNeg F)) F
  | .abs, [F] => lift1 Num.abs (fun F => .abs (Format.opAbs F)) F
  | .logb, [F] => liftCeil c logbFmt F
  | .exp2, [F] => liftCeil c exp2Fmt F
  | .min, [F₁, F₂] => lift2 c Num.min (fun F₁ F₂ => .abs (fmtJoin F₁ F₂)) F₁ F₂
  | .max, [F₁, F₂] => lift2 c Num.max (fun F₁ F₂ => .abs (fmtJoin F₁ F₂)) F₁ F₂
  | .round, [F] | .cast, [F] => F
  | _, _ => .top
def intFormat : Format := { p := ⊤, exp := (0 : ℤ), b := ⊤, specials := ∅ }
def ExactOp.aval (c : Ceiling) : ExactOp → List (AVal (Fmt.domain c)) → AVal (Fmt.domain c)
  | .len, _ => .fmt (.abs intFormat)
  | _, _ => .other
end Fpy


