-- Prove2me | solution 1 for Fpy.equiv_rescale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:53:35.849109+00:00
-- url     : https://prove2.me/submissions/0b8d7884-321a-4880-95c2-165bd57e57b2

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_RoundCtx_round_scale
import Theorems.Thm_Fpy_exec_round
import Theorems.Thm_Fpy_exec_round_inv
import Theorems.Thm_Fpy_Equiv_of_fwd
import Theorems.Thm_Fpy_Eval_num_of_arith
import Theorems.Thm_Fpy_Exec_seq_left
import Theorems.Thm_Fpy_Exec_withCtx_assign
import Theorems.Thm_Fpy_Store_agree_update_of_mem
import Theorems.Thm_Fpy_Val_isCtx_of_rnd
import Theorems.Thm_Fpy_eval_var_inv
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
theorem _root_.solution {C C₀ : Val} {c c₀ : RoundCtx} {ce : Expr (fpy decode)} {x t u m : Var}
    {k : ℤ} (hC : C.rnd (fpy decode) = some c.round) (hce : Denotes Φ ce C₀)
    (hC₀ : C₀.rnd (fpy decode) = some c₀.round) (hsc : c.Scaled c₀ k) :
    Equiv Φ {u, m} Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.seq (.withCtx .real (.assign u (.arithOp .mul [.num (.finite (2 ^ (-k))), .var t])))
        (.seq (.withCtx ce (.assign m (.arithOp .round [.var u])))
          (.withCtx .real (.assign x (.arithOp .mul [.num (.finite (2 ^ k)), .var m]))))) := by
  refine Equiv.of_fwd (fun σ C₁ o _ hκ hs => ?_) (fun σ C₁ o' _ hκ hs => ?_)
  · obtain rfl := hκ C rfl
    obtain ⟨v, ht, rfl⟩ := exec_round_inv hC hs
    set σ₁ := σ.update u (.num (Num.mul (.finite (2 ^ (-k))) v))
    set σ₂ := σ₁.update m (.num (c₀.round (Num.mul (.finite (2 ^ (-k))) v)))
    have h₁ : Exec Φ σ .real (.assign u (.arithOp .mul [.num (.finite (2 ^ (-k))), .var t]))
        (.normal σ₁) :=
      .assign (.arith (ns := [_, _]) (r := id) (.cons .num (.cons (.var ht) .nil)) rfl rfl)
    have h₂ : Exec Φ σ₁ C₀ (.assign m (.arithOp .round [.var u])) (.normal σ₂) :=
      exec_round hC₀ (by simp [σ₁, Store.update])
    have h₃ : Exec Φ σ₂ .real (.assign x (.arithOp .mul [.num (.finite (2 ^ k)), .var m]))
        (.normal (σ₂.update x (.num (c.round v)))) := by
      rw [RoundCtx.round_scale hsc v]
      exact .assign (.arith (ns := [_, _]) (r := id)
        (.cons .num (.cons (.var (by simp [σ₂, Store.update])) .nil)) rfl rfl)
    refine ⟨_, .seqNormal (.withCtx .real trivial h₁)
      (.seqNormal (.withCtx ((hce σ₁ C₀).mpr rfl) (Val.isCtx_of_rnd hC₀) h₂)
        (.withCtx .real trivial h₃)), ?_⟩
    exact Store.Agree.update ((σ.agree_update_of_mem (by simp) _).trans
      (σ₁.agree_update_of_mem (by simp) _)) _ _
  · obtain rfl := hκ C rfl
    obtain ⟨_, h₁⟩ := hs.seq_left
    obtain ⟨_, _, he⟩ := h₁.withCtx_assign
    obtain ⟨u, hu⟩ := he.num_of_arith (by simp : Expr.var t ∈ _)
    exact ⟨_, exec_round hC (eval_var_inv hu)⟩
end Fpy
