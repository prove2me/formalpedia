-- Prove2me | solution 1 for Fpy.equiv_floatToFixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:53:19.840979+00:00
-- url     : https://prove2.me/submissions/12e6d869-efdc-460b-9723-7f35fc0e03d6

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
import Theorems.Thm_Fpy_RoundCtx_round_fixed
import Theorems.Thm_Fpy_exec_round
import Theorems.Thm_Fpy_exec_round_inv
import Theorems.Thm_Fpy_num_canonicalExp
import Theorems.Thm_Fpy_Equiv_of_fwd
import Theorems.Thm_Fpy_Eval_num_of_arith
import Theorems.Thm_Fpy_Exec_seq_left
import Theorems.Thm_Fpy_Exec_withCtx_assign
import Theorems.Thm_Fpy_Store_Agree_update_fresh
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
theorem _root_.solution {C : Val} {c : RoundCtx} {cf : Expr (fpy decode)} {x t n : Var}
    {p : ℕ} (hC : C.rnd (fpy decode) = some c.round) (hp : c.F.p = p) (hp1 : p ≠ 1)
    (hb : c.F.b = ⊤) (hnt : n ≠ t)
    (hcf : ∀ σ (k : ℤ), σ n = some (.num (.finite k)) → ∃ C' c', DenotesAt Φ σ cf C' ∧
      C'.rnd (fpy decode) = some (RoundCtx.round c') ∧ c'.F.p = ⊤ ∧ c'.F.exp = (k : QExp) ∧
      c'.F.b = ⊤ ∧ c'.rm = c.rm)
    (hfin : ∀ σ, Γ.Holds σ → ∀ u, σ t = some (.num u) → ∃ y, u = .finite y ∧ y ≠ 0) :
    Equiv Φ {n} Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.seq (.withCtx .real (.assign n (.arithOp .max
          [.arithOp .add [.arithOp .logb [.var t], .num (.finite (1 - p))],
            .num (qexpNum c.F.exp)])))
        (.withCtx cf (.assign x (.arithOp .round [.var t])))) := by
  refine Equiv.of_fwd (fun σ C₀ o hΓ hκ hs => ?_) (fun σ C₀ o' _ hκ hs => ?_)
  · obtain rfl := hκ C rfl
    obtain ⟨u, ht, rfl⟩ := exec_round_inv hC hs
    obtain ⟨y, rfl, hy⟩ := hfin σ hΓ u ht
    set k := c.F.canonicalExp y
    have hev : Eval Φ σ .real (.arithOp .max
        [.arithOp .add [.arithOp .logb [.var t], .num (.finite (1 - p))],
          .num (qexpNum c.F.exp)]) (.num (.finite (k : ℝ))) := by
      rw [← num_canonicalExp hp hy]
      exact .arith (ns := [_, _]) (r := id) (.cons (.arith (ns := [_, _]) (r := id)
        (.cons (.arith (ns := [_]) (r := id) (.cons (.var ht) .nil) rfl rfl) (.cons .num .nil))
          rfl rfl) (.cons .num .nil)) rfl rfl
    obtain ⟨C', c', hden, hC', hp', he', hb', hrm'⟩ :=
      hcf (σ.update n (.num (.finite (k : ℝ)))) k (by simp [Store.update])
    have ht₁ : (σ.update n (.num (.finite (k : ℝ)))) t = some (.num (.finite y)) := by
      simp [Store.update, Ne.symm hnt, ht]
    have hp1' : c.F.p ≠ ((1 : ℕ) : Prec) := by
      rw [hp]; exact fun h => hp1 (ENat.coe_inj.mp h)
    refine ⟨_, .seqNormal (.withCtx .real trivial (.assign hev))
      (.withCtx ((hden C').mpr rfl) (Val.isCtx_of_rnd hC') (exec_round hC' ht₁)), ?_⟩
    rw [RoundCtx.round_fixed hp1' hb hp' hb' hrm' he']
    exact Store.Agree.update_fresh _ _ _
  · obtain rfl := hκ C rfl
    obtain ⟨_, h₁⟩ := hs.seq_left
    obtain ⟨_, _, he⟩ := h₁.withCtx_assign
    obtain ⟨_, he⟩ := he.num_of_arith (List.mem_cons_self ..)
    obtain ⟨_, he⟩ := he.num_of_arith (List.mem_cons_self ..)
    obtain ⟨u, hu⟩ := he.num_of_arith (List.mem_singleton_self _)
    exact ⟨_, exec_round hC (eval_var_inv hu)⟩
end Fpy
