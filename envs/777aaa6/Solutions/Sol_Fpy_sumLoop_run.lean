-- Prove2me | solution 1 for Fpy.sumLoop_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:25:52.360661+00:00
-- url     : https://prove2.me/submissions/ee083c28-9422-4825-ae6b-7bee467739e0

import Definitions.Def_Fpy_Semantics
import Definitions.Def_Fpy_Ops
import Definitions.Def_Fpy_Sum
import Theorems.Thm_Fpy_sumVal_take_succ
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
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
variable {C : Val} {r : Num → Num} (hr : C.rnd (fpy decode) = some r) (us : List Num)
include hr
namespace Fpy
theorem _root_.solution : ∀ j k, us.length - k = j → 1 ≤ k → k ≤ us.length →
    Exec Φ (sumStore us (sumVal r (us.take k)) k) C sumLoop
      (.normal (sumStore us (sumVal r us) us.length)) := by
  have hxs : ∀ p k, sumStore us p k "xs" = some (.list (us.map .num)) := by
    intro p k; simp [sumStore, Store.update, Store.single]
  have hlen : ∀ p k, Eval Φ (sumStore us p k) C (.exactOp .len [.var "xs"])
      (.num (.finite us.length)) := fun p k =>
    .exact (.cons (.var (hxs p k)) .nil) (by simp [fpy, ExactOp.eval])
  have hi : ∀ p k, sumStore us p k "i" = some (.num (.finite k)) := by
    intro p k; simp [sumStore, Store.update]
  have hguard : ∀ p k, Eval Φ (sumStore us p k) C
      (.exactOp .lt [.var "i", .exactOp .len [.var "xs"]]) (.bool (decide (k < us.length))) :=
    fun p k => .exact (.cons (.var (hi p k)) (.cons (hlen p k) .nil)) (by simp [fpy, ExactOp.eval,
      Num.lt])
  intro j
  induction j with
  | zero =>
    intro k hj _ hkL
    obtain rfl : k = us.length := by omega
    rw [List.take_length]
    exact .whileFalse (by simpa using hguard (sumVal r us) us.length)
  | succ j ih =>
    intro k hj hk _
    have hkL : k < us.length := by omega
    set p := sumVal r (us.take k)
    have hs : sumStore us p k "s" = some (.num p) := by simp [sumStore, Store.update]
    have hidx : Eval Φ (sumStore us p k) C (.index (.var "xs") (.var "i")) (.num us[k]) :=
      .index (.var (hxs p k)) (.var (hi p k)) (by simp [hkL])
    have h₁ : Exec Φ (sumStore us p k) C
        (.assign "s" (.arithOp .add [.var "s", .index (.var "xs") (.var "i")]))
        (.normal ((sumStore us p k).update "s" (.num (r (Num.add p us[k]))))) :=
      .assign (.arith (ns := [p, us[k]]) (.cons (.var hs) (.cons hidx .nil)) rfl hr)
    have h₂ : Exec Φ ((sumStore us p k).update "s" (.num (r (Num.add p us[k])))) C
        (.withCtx .real (.assign "i" (.arithOp .add [.var "i", .num (.finite 1)])))
        (.normal (sumStore us (r (Num.add p us[k])) (k + 1))) := by
      have h : Exec Φ ((sumStore us p k).update "s" (.num (r (Num.add p us[k])))) C
          (.withCtx .real (.assign "i" (.arithOp .add [.var "i", .num (.finite 1)])))
          (.normal (((sumStore us p k).update "s" (.num (r (Num.add p us[k])))).update "i"
            (.num (id (Num.add (.finite k) (.finite 1)))))) :=
        .withCtx .real trivial (.assign (.arith (ns := [.finite k, .finite 1]) (r := id)
          (.cons (.var (by simp [sumStore, Store.update])) (.cons .num .nil)) rfl rfl))
      convert h using 2
      funext x
      simp only [sumStore, Store.update, Function.update_apply, id, Num.add]
      split_ifs <;> simp_all
    have h₃ := ih (k + 1) (by omega) (by omega) (by omega)
    rw [sumVal_take_succ r hk hkL] at h₃
    exact .whileTrue (by simpa [hkL] using hguard p k) (.seqNormal (.seqNormal h₁ h₂) h₃)
end Fpy
