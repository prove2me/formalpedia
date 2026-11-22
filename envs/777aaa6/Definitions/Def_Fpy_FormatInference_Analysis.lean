-- Prove2me | Definitions.Def_Fpy_FormatInference_Analysis
-- name    : Fpy_FormatInference_Analysis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:12:39.969784+00:00
-- url     : https://prove2.me/theorems/614ea4dc-a40d-46e1-9652-cad2483125b1
-- title:
--   Analysis
-- statement:
--   Definitions and structural lemmas for Analysis, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Analysis.lean

import Definitions.Def_Fpy_FormatInference_Refine
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
variable {decode : List (Label × Val) → Option RoundCtx} {c : Ceiling}
open Classical in
mutual

/-- The value an abstract value pins down, if it pins one down: a singleton set,
a known context, or a record of these. -/
noncomputable def AVal.const? : AVal (Fmt.domain c) → Option Val
  | .fmt F =>
    match (show Fmt from F) with
    | .set S => if h : ∃ n, S = {n} then some (.num (Classical.choose h)) else none
    | _ => none
  | .record afs => (AVal.constFields afs).map .record
  | .known C => some C
  | _ => none

noncomputable def AVal.constFields :
    List (Label × AVal (Fmt.domain c)) → Option (List (Label × Val))
  | [] => some []
  | (l, a) :: afs => do
    let v ← a.const?
    let vs ← AVal.constFields afs
    pure ((l, v) :: vs)

end
mutual

theorem Describes.eq_of_const? {a : AVal (Fmt.domain c)} {v w : Val} :
    Describes a v → a.const? = some w → v = w
  | .fmt (F := F) (n := n) h, hw => by
    unfold AVal.const? at hw
    split at hw
    · next S hS =>
      split at hw
      · next hn =>
        simp only [Option.some.injEq] at hw
        subst hw
        have hmem : n ∈ (show Fmt from F).γ := h
        rw [hS, Classical.choose_spec hn] at hmem
        rw [Finset.mem_singleton.mp hmem]
      · simp at hw
    · simp at hw
  | .record (fs := fs) h, hw => by
    simp only [AVal.const?, Option.map_eq_some_iff] at hw
    obtain ⟨ws, hws, rfl⟩ := hw
    rw [DescribesFields.eq_of_constFields h hws]
  | .known, hw => by simpa [AVal.const?] using hw
  | .list _, hw | .bool, hw | .real, hw | .ctx, hw | .top, hw => by simp [AVal.const?] at hw

theorem DescribesFields.eq_of_constFields {afs : List (Label × AVal (Fmt.domain c))}
    {fs ws : List (Label × Val)} :
    DescribesFields afs fs → AVal.constFields afs = some ws → fs = ws
  | .nil, hw => by simpa [AVal.constFields] using hw
  | .cons (l := l) hd tl, hw => by
    simp only [AVal.constFields, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hw
    obtain ⟨v, hv, vs, hvs, rfl⟩ := hw
    rw [Describes.eq_of_const? hd hv, DescribesFields.eq_of_constFields tl hvs]

end
noncomputable def ctxOfAVal (a : AVal (Fmt.domain c)) : Option Val :=
  match a.const? with
  | some (.record fs) => some (.ctx fs)
  | _ => none
variable (decode c) in
/-- Format inference for FPy, for a choice of `⌈S⌉`. -/
noncomputable def fpyAnalysis : Analysis (fpy decode) (Fmt.domain c) where
  arith := ArithOp.fmt c
  exact := ExactOp.aval c
  ctxFmt := fpyCtxFmt decode
  ctxOf := ctxOfAVal
  refine := refine
end Fpy


