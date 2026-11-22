-- Prove2me | solution 1 for Fpy.equiv_overflow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:52:55.769114+00:00
-- url     : https://prove2.me/submissions/cb21d7e2-c8bd-4e70-9edf-d46bfb5c1784

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_RoundCtx_round_of_overflows
import Theorems.Thm_Fpy_RoundCtx_round_of_not_overflows
import Theorems.Thm_Fpy_exec_round
import Theorems.Thm_Fpy_exec_round_inv
import Theorems.Thm_Fpy_eval_numCmp
import Theorems.Thm_Fpy_le_of_numCmp
import Theorems.Thm_Fpy_num_of_cmp
import Theorems.Thm_Fpy_Equiv_of_fwd
import Theorems.Thm_Fpy_Exec_ite_guard
import Theorems.Thm_Fpy_Val_isCtx_of_rnd
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
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}
namespace Fpy
theorem _root_.solution {C C' : Val} {c c' : RoundCtx} {ce : Expr (fpy decode)} {x t : Var}
    {sp sn : Bool} {τp τn : ℝ} (hC : C.rnd (fpy decode) = some c.round) (hce : Denotes Φ ce C')
    (hC' : C'.rnd (fpy decode) = some c'.round) (hF : c'.F = c.F.unbounded) (hrm : c'.rm = c.rm)
    (hτp : 0 ≤ τp) (hτn : τn < 0)
    (hτ : ∀ y, Overflows c.F c.rm y ↔
      numCmp sp (.finite τp) (.finite y) = true ∨ numCmp sn (.finite y) (.finite τn) = true)
    (hfin : ∀ σ, Γ.Holds σ → ∀ u, σ t = some (.num u) → ∃ y, u = .finite y) :
    Equiv Φ X Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.ite (.exactOp (cmpOp sp) [.num (.finite τp), .var t])
        (.assign x (.num (c.O.map false).toReal))
        (.ite (.exactOp (cmpOp sn) [.var t, .num (.finite τn)])
          (.assign x (.num (c.O.map true).toReal))
          (.withCtx ce (.assign x (.arithOp .round [.var t]))))) := by
  refine Equiv.of_fwd (fun σ C₀ o hΓ hκ hs => ?_) (fun σ C₀ o' _ hκ hs => ?_) <;>
    obtain rfl := hκ C rfl
  · obtain ⟨u, ht, rfl⟩ := exec_round_inv hC hs
    obtain ⟨y, rfl⟩ := hfin σ hΓ u ht
    refine ⟨.normal (σ.update x (.num (c.round (.finite y)))), ?_, Store.Agree.refl _⟩
    have hp := eval_numCmp (Φ := Φ) (C := C) sp (.num (n := .finite τp)) (.var ht)
    have hn := eval_numCmp (Φ := Φ) (C := C) sn (.var ht) (.num (n := .finite τn))
    cases hgp : numCmp sp (.finite τp) (.finite y)
    · cases hgn : numCmp sn (.finite y) (.finite τn)
      · refine .iteFalse (hgp ▸ hp) (.iteFalse (hgn ▸ hn) ?_)
        rw [← RoundCtx.round_of_not_overflows hF hrm (by simp [hτ, hgp, hgn])]
        exact .withCtx ((hce σ C').mpr rfl) (Val.isCtx_of_rnd hC') (exec_round hC' ht)
      · refine .iteFalse (hgp ▸ hp) (.iteTrue (hgn ▸ hn) ?_)
        rw [c.round_of_overflows ((hτ y).mpr (.inr hgn)),
          decide_eq_true ((le_of_numCmp hgn).trans_lt hτn)]
        exact .assign .num
    · refine .iteTrue (hgp ▸ hp) ?_
      rw [c.round_of_overflows ((hτ y).mpr (.inl hgp)),
        decide_eq_false (not_lt.mpr (hτp.trans (le_of_numCmp hgp)))]
      exact .assign .num
  · obtain ⟨_, he⟩ := hs.ite_guard
    obtain ⟨u, ht⟩ := num_of_cmp he
    exact ⟨_, exec_round hC ht⟩
end Fpy
