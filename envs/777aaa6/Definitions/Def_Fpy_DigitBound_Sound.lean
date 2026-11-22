-- Prove2me | Definitions.Def_Fpy_DigitBound_Sound
-- name    : Fpy_DigitBound_Sound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:40:50.960349+00:00
-- url     : https://prove2.me/theorems/146b1372-106d-45b2-a7c2-782b5e06ec24
-- title:
--   Sound
-- statement:
--   Definitions and structural lemmas for Sound, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Theorems.Thm_Fpy_DigitBound_AgreeOut_agree
import Theorems.Thm_Fpy_DigitBound_Con_P_between
import Theorems.Thm_Fpy_DigitBound_Con_P_ext
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_grow
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_single
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_without
import Theorems.Thm_Fpy_DigitBound_DescribesAll_mem
import Theorems.Thm_Fpy_DigitBound_DescribesFields_lookup
import Theorems.Thm_Fpy_DigitBound_EInt_top_add_coe
import Theorems.Thm_Fpy_DigitBound_ExactOp_eval_bool
import Theorems.Thm_Fpy_DigitBound_ExactOp_eval_len
import Theorems.Thm_Fpy_DigitBound_Fresh_mono_right
import Theorems.Thm_Fpy_DigitBound_LsbAt_le
import Theorems.Thm_Fpy_DigitBound_NumIn_eq
import Theorems.Thm_Fpy_DigitBound_NumIn_term
import Theorems.Thm_Fpy_DigitBound_NumIn_withTerm
import Theorems.Thm_Fpy_DigitBound_Term_eval_congr
import Theorems.Thm_Fpy_DigitBound_Within_grow
import Theorems.Thm_Fpy_DigitBound_add_numOfE
import Theorems.Thm_Fpy_DigitBound_admits_congr
import Theorems.Thm_Fpy_DigitBound_ctxOf_admits
import Theorems.Thm_Fpy_DigitBound_ctxOf_below
import Theorems.Thm_Fpy_DigitBound_describesAll_of_le
import Theorems.Thm_Fpy_DigitBound_eval_update
import Theorems.Thm_Fpy_DigitBound_fresh_bounds
import Theorems.Thm_Fpy_DigitBound_fresh_numIn
import Theorems.Thm_Fpy_DigitBound_logb_eq
import Theorems.Thm_Fpy_DigitBound_lsbOf_abs
import Theorems.Thm_Fpy_DigitBound_lsbOf_neg
import Theorems.Thm_Fpy_DigitBound_max_numOfE
import Theorems.Thm_Fpy_DigitBound_min_numOfE
import Theorems.Thm_Fpy_DigitBound_msbOf_abs
import Theorems.Thm_Fpy_DigitBound_msbOf_neg
import Theorems.Thm_Fpy_DigitBound_neg_numOfE
import Theorems.Thm_Fpy_DigitBound_numOfE_bot
import Theorems.Thm_Fpy_DigitBound_numOfE_coe
import Theorems.Thm_Fpy_DigitBound_numOfE_top
import Theorems.Thm_Fpy_Exec_frame
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
import Theorems.Thm_P2M_Fpy_DigitBound_forall__one_4f65dee80d02
import Theorems.Thm_P2M_Fpy_DigitBound_forall__two_f1f6dda74e3c
attribute [local simp] Fpy.DigitBound.EInt.top_add_coe
attribute [local simp] Fpy.DigitBound.lsbOf_abs
attribute [local simp] Fpy.DigitBound.lsbOf_neg
attribute [local simp] Fpy.DigitBound.msbOf_abs
attribute [local simp] Fpy.DigitBound.msbOf_neg
attribute [local simp] Fpy.DigitBound.numOfE_bot
attribute [local simp] Fpy.DigitBound.numOfE_coe
attribute [local simp] Fpy.DigitBound.numOfE_top
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
namespace Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
theorem ctxBelow_real (n : ℕ) : CtxBelow n (some SCtx.real) :=
  fun K hK => by obtain rfl := Option.mem_some_iff.mp hK; trivial
mutual

theorem DEval.wf {Δ : DEnv} {Γ : AEnv D} {κ : Option SCtx} {χ : Option Val}
    {Ψg : List Con} {n₀ : ℕ}
    {e : Expr (fpy decode)} {d : DVal} {Ψ : List Con} {n₁ : ℕ} :
    DEval decode Φ A Δ Γ κ χ Ψg n₀ e d Ψ n₁ →
      Fresh n₀ n₁ Ψ ∧ (Δ.Below n₀ → CtxBelow n₀ κ → d.Below n₁)
  | .const hτ => ⟨Fresh.nil _, fun _ _ => ⟨trivial, trivial, fun t ht => by
      obtain ⟨z, rfl, -⟩ := hτ t ht
      trivial⟩⟩
  | .bool => ⟨Fresh.nil _, fun _ _ => trivial⟩
  | .real => ⟨Fresh.nil _, fun _ _ => trivial⟩
  | .var hx => ⟨Fresh.nil _, fun hΔ _ => hΔ _ _ hx⟩
  | .list hl _ hF hdb => ⟨(DEvalList.wf hl).1.append hF, fun _ _ => ⟨hF.le, hdb⟩⟩
  | .index h₁ h₂ _ hF hb => ⟨((DEval.wf h₁).1.append (DEval.wf h₂).1).append hF, fun _ _ => hb⟩
  | .record hf => ⟨(DEvalFields.wf hf).1, fun hΔ hκ => (DEvalFields.wf hf).2 hΔ hκ⟩
  | .proj h hl => ⟨(DEval.wf h).1, fun hΔ hκ => DVal.BelowFields.lookup ((DEval.wf h).2 hΔ hκ) hl⟩
  | .ctx (d := d) h => ⟨(DEval.wf h).1, fun hΔ hκ => by
      cases hc : ctxOf d with
      | none => trivial
      | some C => exact ctxOf_below ((DEval.wf h).2 hΔ hκ) hc⟩
  | .arith hl _ hF hlb hmb => ⟨(DEvalList.wf hl).1.append hF, fun _ _ =>
      ⟨hlb, hmb, fun t ht => absurd ht (by simp)⟩⟩
  | .linear (op := op) hop hl _ hF hlb hmb => ⟨(DEvalList.wf hl).1.append hF, fun hΔ hκ => by
      have hb := (DEvalList.wf hl).2 hΔ hκ
      have h₁ := (hb _ (List.mem_cons_self ..)).2.2 _ rfl
      have h₂ := (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2.2 _ rfl
      have hle := hF.le
      refine ⟨hlb, hmb, fun t ht => ?_⟩
      obtain rfl := Option.mem_some_iff.mp ht
      split <;> exact ⟨h₁.mono hle, h₂.mono hle⟩⟩
  | .neg hl _ hF hlb hmb => ⟨(DEvalList.wf hl).1.append hF, fun hΔ hκ => by
      have h₁ := ((DEvalList.wf hl).2 hΔ hκ _ (List.mem_cons_self ..)).2.2 _ rfl
      refine ⟨hlb, hmb, fun t ht => ?_⟩
      obtain rfl := Option.mem_some_iff.mp ht
      exact Term.Below.mono hF.le h₁⟩
  | .logb hl _ hF hlb hmb => ⟨(DEvalList.wf hl).1.append hF, fun hΔ hκ => by
      have h₁ := ((DEvalList.wf hl).2 hΔ hκ _ (List.mem_cons_self ..)).2.1
      refine ⟨hlb, hmb, fun t ht => ?_⟩
      obtain rfl := Option.mem_some_iff.mp ht
      exact h₁.mono hF.le⟩
  | .ext (n₂ := n₂) _ _ _ hl _ hF hlb hmb =>
      ⟨((DEvalList.wf hl).1.append hF).append (Fresh.single n₂ rfl), fun _ _ =>
        ⟨hlb.mono (Nat.le_succ _), hmb.mono (Nat.le_succ _), fun t ht => by
          obtain rfl := Option.mem_some_iff.mp ht
          exact Nat.lt_succ_self _⟩⟩
  | .exact hl _ => ⟨(DEvalList.wf hl).1, fun _ _ => trivial⟩
  | .len hl => ⟨(DEvalList.wf hl).1.mono_right (by omega), fun _ _ =>
      ⟨show _ < _ by omega, show _ < _ by omega, fun t ht => absurd ht (by simp)⟩⟩
  | .call _ he _ hs => ⟨(DEval.wf he).1.append (DExec.wf hs).1, fun hΔ hκ =>
      ((DExec.wf hs).2 (DEnv.Below.single ((DEval.wf he).2 hΔ hκ))
        (hκ.mono (DEval.wf he).1.le)).2 _ rfl⟩
  | .int (n₁ := n₁) _ h _ _ => ⟨(DEval.wf h).1.append (Fresh.single n₁ rfl), fun hΔ hκ =>
      have hb := (DEval.wf h).2 hΔ hκ
      ⟨hb.1.mono (Nat.le_succ _), hb.2.1.mono (Nat.le_succ _), fun t ht => by
        obtain rfl := Option.mem_some_iff.mp ht
        exact Nat.lt_succ_self _⟩⟩
  | .fmt (n₁ := n₁) h _ _ _ _ => ⟨(DEval.wf h).1.append (fresh_bounds n₁ _ _), fun hΔ hκ =>
      ⟨show _ < _ by omega, show _ < _ by omega, fun t ht =>
        ((DEval.wf h).2 hΔ hκ).2.2 t ht |>.mono (by omega)⟩⟩
termination_by structural h => h

theorem DEvalList.wf {Δ : DEnv} {Γ : AEnv D} {κ : Option SCtx} {χ : Option Val}
    {Ψg : List Con} {n₀ : ℕ}
    {es : List (Expr (fpy decode))} {ds : List DVal} {Ψ : List Con} {n₁ : ℕ} :
    DEvalList decode Φ A Δ Γ κ χ Ψg n₀ es ds Ψ n₁ →
      Fresh n₀ n₁ Ψ ∧ (Δ.Below n₀ → CtxBelow n₀ κ → ∀ d ∈ ds, d.Below n₁)
  | .nil => ⟨Fresh.nil _, fun _ _ _ h => absurd h List.not_mem_nil⟩
  | .cons h hs => ⟨(DEval.wf h).1.append (DEvalList.wf hs).1, fun hΔ hκ => by
      have h₀₁ := (DEval.wf h).1.le
      have hd₀ := ((DEval.wf h).2 hΔ hκ).mono (DEvalList.wf hs).1.le
      have hds := (DEvalList.wf hs).2 (hΔ.mono h₀₁) (hκ.mono h₀₁)
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hd₀
      · exact hds d hd⟩
termination_by structural h => h

theorem DEvalFields.wf {Δ : DEnv} {Γ : AEnv D} {κ : Option SCtx} {χ : Option Val}
    {Ψg : List Con} {n₀ : ℕ}
    {fs : List (Label × Expr (fpy decode))} {afs : List (Label × DVal)} {Ψ : List Con} {n₁ : ℕ} :
    DEvalFields decode Φ A Δ Γ κ χ Ψg n₀ fs afs Ψ n₁ →
      Fresh n₀ n₁ Ψ ∧ (Δ.Below n₀ → CtxBelow n₀ κ → DVal.BelowFields n₁ afs)
  | .nil => ⟨Fresh.nil _, fun _ _ => trivial⟩
  | .cons h hs => ⟨(DEval.wf h).1.append (DEvalFields.wf hs).1, fun hΔ hκ =>
      have h₀₁ := (DEval.wf h).1.le
      ⟨((DEval.wf h).2 hΔ hκ).mono (DEvalFields.wf hs).1.le,
        (DEvalFields.wf hs).2 (hΔ.mono h₀₁) (hκ.mono h₀₁)⟩⟩
termination_by structural h => h

theorem DExec.wf {Δ : DEnv} {Γ : AEnv D} {κ : Option SCtx} {χ : Option Val}
    {Ψg : List Con} {n₀ : ℕ}
    {s : Stmt (fpy decode)} {Δ' : DEnv}
    {a : Option DVal} {Ψ : List Con} {n₁ : ℕ} :
    DExec decode Φ A Δ Γ κ χ Ψg n₀ s Δ' a Ψ n₁ →
      Fresh n₀ n₁ Ψ ∧ (Δ.Below n₀ → CtxBelow n₀ κ → Δ'.Below n₁ ∧ RetBelow n₁ a)
  | .assign h => ⟨(DEval.wf h).1, fun hΔ hκ =>
      ⟨(hΔ.mono (DEval.wf h).1.le).update _ ((DEval.wf h).2 hΔ hκ), fun _ h => absurd h (by simp)⟩⟩
  | .skip => ⟨Fresh.nil _, fun hΔ _ => ⟨hΔ, fun _ h => absurd h (by simp)⟩⟩
  | .ret h => ⟨(DEval.wf h).1, fun hΔ hκ => by
      have hd₀ := (DEval.wf h).2 hΔ hκ
      exact ⟨hΔ.mono (DEval.wf h).1.le, fun _ hd => Option.mem_some_iff.mp hd ▸ hd₀⟩⟩
  | .assert h => ⟨(DEval.wf h).1, fun hΔ _ =>
      ⟨hΔ.mono (DEval.wf h).1.le, fun _ h => absurd h (by simp)⟩⟩
  | .seq h₁ _ h₂ _ _ hF ha => ⟨((DExec.wf h₁).1.append (DExec.wf h₂).1).append hF, fun hΔ hκ =>
      have h₀₁ := (DExec.wf h₁).1.le
      ⟨(((DExec.wf h₂).2 ((DExec.wf h₁).2 hΔ hκ).1 (hκ.mono h₀₁)).1).mono hF.le, ha⟩⟩
  | .ite h₁ h₂ _ _ _ _ hF hΔ' ha => ⟨((DExec.wf h₁).1.append (DExec.wf h₂).1).append hF,
      fun _ _ => ⟨hΔ', ha⟩⟩
  | .whileDo _ hFᵢ hbᵢ _ _ _ hs => ⟨hFᵢ.append (DExec.wf hs).1, fun _ hκ =>
      ⟨hbᵢ.mono (DExec.wf hs).1.le, ((DExec.wf hs).2 hbᵢ (hκ.mono hFᵢ.le)).2⟩⟩
  | .withCtx he _ hs => ⟨(DEval.wf he).1.append (DExec.wf hs).1, fun hΔ _ => by
      have hC₀ := (DEval.wf he).2 hΔ (ctxBelow_real _)
      exact (DExec.wf hs).2 (hΔ.mono (DEval.wf he).1.le)
        (fun C hC => Option.mem_some_iff.mp hC ▸ hC₀)⟩
  | .withUnknown he _ hs => ⟨(DEval.wf he).1.append (DExec.wf hs).1, fun hΔ _ =>
      (DExec.wf hs).2 (hΔ.mono (DEval.wf he).1.le) (fun _ h => absurd h (by simp))⟩
termination_by structural h => h

end
local notation "nan" => (WithSpecial.special Special.nan : Num)
theorem numIns {Ψ : List Con} {ι : Asgn} :
    ∀ {Is : List (Term × Term × Option Term)} {ns : List Num},
    List.Forall₂ (Describes Ψ ι) (Is.map fun I => .num I.1 I.2.1 I.2.2) (ns.map .num) →
    List.Forall₂ (fun (I : Term × Term × Option Term) n => NumIn ι I.1 I.2.1 I.2.2 n) Is ns
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h hs => by
    cases h with
    | num h => exact .cons h (numIns hs)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
theorem args_one {Ψ : List Con} {ι : Asgn} {l m : Term} {τ : Option Term} {ns : List Num}
    (h : List.Forall₂ (Describes Ψ ι) [.num l m τ] (ns.map .num)) :
    ∃ u, ns = [u] ∧ NumIn ι l m τ u := by
  obtain ⟨u, rfl, hu⟩ := forall₂_one (numIns (Is := [(l, m, τ)]) h); exact ⟨u, rfl, hu⟩
theorem args_two {Ψ : List Con} {ι : Asgn} {l₁ m₁ l₂ m₂ : Term} {τ₁ τ₂ : Option Term}
    {ns : List Num}
    (h : List.Forall₂ (Describes Ψ ι) [.num l₁ m₁ τ₁, .num l₂ m₂ τ₂] (ns.map .num)) :
    ∃ u₁ u₂, ns = [u₁, u₂] ∧ NumIn ι l₁ m₁ τ₁ u₁ ∧ NumIn ι l₂ m₂ τ₂ u₂ := by
  obtain ⟨u₁, u₂, rfl, h₁, h₂⟩ := forall₂_two (numIns (Is := [(l₁, m₁, τ₁), (l₂, m₂, τ₂)]) h)
  exact ⟨u₁, u₂, rfl, h₁, h₂⟩
theorem add_term {u₁ u₂ : Num} {a b : EInt} (h₁ : u₁ = nan ∨ u₁ = numOfE a)
    (h₂ : u₂ = nan ∨ u₂ = numOfE b) : Num.add u₁ u₂ = nan ∨ Num.add u₁ u₂ = numOfE (a + b) := by
  rcases h₁ with rfl | rfl
  · left; rcases u₂ with _ | (_ | _) <;> rfl
  · rcases h₂ with rfl | rfl
    · left; cases a using WithBotTop.rec <;> rfl
    · exact add_numOfE a b
theorem neg_term {u : Num} {a : EInt} (h : u = nan ∨ u = numOfE a) :
    Num.neg u = nan ∨ Num.neg u = numOfE (negE a) := by
  rcases h with rfl | rfl
  · exact .inl rfl
  · exact .inr (neg_numOfE a)
theorem ext_term {u₁ u₂ : Num} {a b : EInt} (ge : Bool) (h₁ : u₁ = nan ∨ u₁ = numOfE a)
    (h₂ : u₂ = nan ∨ u₂ = numOfE b) :
    (if ge then Num.max u₁ u₂ else Num.min u₁ u₂) = nan ∨
      (if ge then Num.max u₁ u₂ else Num.min u₁ u₂) = numOfE (if ge then max a b else min a b) := by
  rcases h₁ with rfl | rfl
  · left; cases ge <;> rcases u₂ with _ | (_ | _) <;> rfl
  · rcases h₂ with rfl | rfl
    · left; cases ge <;> cases a using WithBotTop.rec <;> rfl
    · right; cases ge
      · exact min_numOfE a b
      · exact max_numOfE a b
theorem logb_term {ι : Asgn} {l m : Term} {τ : Option Term} {u : Num} (h : NumIn ι l m τ u) :
    Num.logb u = nan ∨ Num.logb u = numOfE (m.eval ι) := by
  rcases h with rfl | ⟨-, hm, -⟩
  · exact .inl rfl
  · by_cases hu : u = nan
    · subst hu; exact .inl rfl
    · exact .inr (by rw [logb_eq hu, hm])
theorem admits_real {ι : Asgn} {C : Val} (h : ∀ K ∈ some SCtx.real, K.Admits ι C) : C = .real :=
  h _ rfl
theorem admits_real' (ι : Asgn) : ∀ K ∈ some SCtx.real, K.Admits ι .real :=
  fun K hK => by obtain rfl := Option.mem_some_iff.mp hK; rfl
theorem knownCtx_admits {a : AVal D} {v : Val} (h : Fpy.Describes a v) :
    Admits (knownCtx a) v := by
  cases a with
  | known C => cases h; exact admits_some _
  | _ => exact admits_none _
theorem step {n₀ n₁ : ℕ} {Ψg Ψ : List Con} {ι ι₁ : Asgn} (hb : Before n₀ Ψg) (hs : Sat ι Ψg)
    (hF : Fresh n₀ n₁ Ψ) (a : Agree n₀ ι ι₁) (hs₁ : Sat ι₁ Ψ) :
    Before n₁ (Ψg ++ Ψ) ∧ Sat ι₁ (Ψg ++ Ψ) :=
  ⟨hb.append hF, (Sat.congr hb a hs).append hs₁⟩
theorem ret_join {n₂ n₃ : ℕ} {Ψg Ψ : List Con} {ι : Asgn} {a₁ a : Option DVal} {v : Val}
    (hw : ∃ d ∈ a₁, Describes Ψg ι d v) (hb : Before n₂ Ψg) (hs : Sat ι Ψg)
    (hra : RetLe n₂ n₃ Ψg Ψ a₁ a) :
    ∃ ι', Agree n₂ ι ι' ∧ Sat ι' Ψ ∧ ∃ d ∈ a, Describes (Ψg ++ Ψ) ι' d v := by
  obtain ⟨d, hd, hv⟩ := hw
  obtain ⟨d', hd', hle⟩ := hra d hd
  obtain ⟨ι', h, hs', hv'⟩ := hle hb ι v hs hv
  exact ⟨ι', h.agree, hs', d', hd', hv'⟩
theorem within_seq {n₂ n₃ : ℕ} {Ψg Ψ : List Con} {ι : Asgn} {Δ : DEnv} {a₂ a : Option DVal}
    {o : Outcome} (hw : Within Ψg ι Δ a₂ o) (hb : Before n₂ Ψg) (hs : Sat ι Ψg)
    (hΔ : Δ.Below n₂) (ha : RetBelow n₂ a₂) (hF : Fresh n₂ n₃ Ψ) (hra : RetLe n₂ n₃ Ψg Ψ a₂ a) :
    ∃ ι', Agree n₂ ι ι' ∧ Sat ι' Ψ ∧ Within (Ψg ++ Ψ) ι' Δ a o := by
  cases o with
  | normal σ =>
    obtain ⟨ι', h, hs'⟩ := Sat.extend hF ι
    exact ⟨ι', h, hs', hw.grow hb hF h hΔ ha⟩
  | ret v => exact ret_join hw hb hs hra
theorem within_join {n₂ n₃ : ℕ} {Ψg Ψ : List Con} {ι : Asgn} {Δ₁ Δ' : DEnv}
    {a₁ a : Option DVal} {o : Outcome} (hw : Within Ψg ι Δ₁ a₁ o) (hb : Before n₂ Ψg)
    (hs : Sat ι Ψg) (hle : DEnv.Le n₂ n₃ Ψg Ψ Δ₁ Δ') (hra : RetLe n₂ n₃ Ψg Ψ a₁ a) :
    ∃ ι', Agree n₂ ι ι' ∧ Sat ι' Ψ ∧ Within (Ψg ++ Ψ) ι' Δ' a o := by
  cases o with
  | normal σ =>
    obtain ⟨ι', h, hs', hσ⟩ := hle hb ι σ hs hw
    exact ⟨ι', h.agree, hs', hσ⟩
  | ret v => exact ret_join hw hb hs hra
theorem chain {P : Asgn → Prop} {n₀ n₁ : ℕ} {Ψ Ψ' : List Con} {ι ι₁ ι₂ : Asgn}
    (hF : Fresh n₀ n₁ Ψ) (a₁ : Agree n₀ ι ι₁) (hs₁ : Sat ι₁ Ψ) (a₂ : Agree n₁ ι₁ ι₂)
    (hs₂ : Sat ι₂ Ψ') (h : P ι₂) : ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ') ∧ P ι' :=
  ⟨ι₂, a₁.trans (a₂.mono hF.le), (Sat.congr hF.before a₂ hs₁).append hs₂, h⟩
theorem chain₃ {P : Asgn → Prop} {n₀ n₁ n₂ : ℕ} {Ψ₁ Ψ₂ Ψ₃ : List Con} {ι ι₁ ι₂ ι₃ : Asgn}
    (hF₁ : Fresh n₀ n₁ Ψ₁) (hF₂ : Fresh n₁ n₂ Ψ₂) (a₁ : Agree n₀ ι ι₁) (hs₁ : Sat ι₁ Ψ₁)
    (a₂ : Agree n₁ ι₁ ι₂) (hs₂ : Sat ι₂ Ψ₂) (a₃ : Agree n₂ ι₂ ι₃) (hs₃ : Sat ι₃ Ψ₃) (h : P ι₃) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ₁ ++ Ψ₂ ++ Ψ₃) ∧ P ι' :=
  chain (hF₁.append hF₂) (a₁.trans (a₂.mono hF₁.le)) ((Sat.congr hF₁.before a₂ hs₁).append hs₂)
    a₃ hs₃ h
section Rules
variable {Δ : DEnv} {Γ : AEnv D} {χ : Option Val} {n₀ n₁ n₂ : ℕ} {Ψg Ψ Ψ' : List Con} {ι : Asgn}
  {C : Val} {ns : List Num}
  {u : Num} {r : Num → Num} {l m l₁ m₁ l₂ m₂ τ₁ τ₂ : Term}
theorem linear_sound {op : ArithOp} {e₁ e₂ : Expr (fpy decode)} (hop' : op = .add ∨ op = .sub)
    (hdl : DEvalList decode Φ A Δ Γ (some .real) χ Ψg n₀ [e₁, e₂]
      [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] Ψ n₁)
    (hok : ArithOK decode (some .real) op [(l₁, m₁, some τ₁), (l₂, m₂, some τ₂)] n₁ n₂ Ψ' l m)
    (hΔ : Δ.Below n₀)
    (hop : (fpy decode).arith op ns = some u) (hr : C.rnd (fpy decode) = some r)
    (hC : ∀ K ∈ some SCtx.real, K.Admits ι C)
    (ih : ∃ ι₁, Agree n₀ ι ι₁ ∧ Sat ι₁ Ψ ∧
      List.Forall₂ (Describes (Ψg ++ Ψ) ι₁) [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)]
        (ns.map .num)) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ') ∧ Describes (Ψg ++ (Ψ ++ Ψ')) ι'
      (.num l m (some (if op = .add then .add τ₁ τ₂ else .add τ₁ (.neg τ₂)))) (.num (r u)) := by
  obtain ⟨ι₁, a₁, hs₁, hds⟩ := ih
  obtain rfl := admits_real hC
  obtain rfl : _ = id := (Option.some.inj hr).symm
  have hb := (DEvalList.wf hdl).2 hΔ (ctxBelow_real _)
  have hτ₁ := (hb _ (List.mem_cons_self ..)).2.2 _ rfl
  have hτ₂ := (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2.2 _ rfl
  obtain ⟨u₁, u₂, rfl, hu₁, hu₂⟩ := args_two hds
  obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (.cons hu₁ (.cons hu₂ .nil)) hop
    (admits_real' _) rfl
  have e₁ := Term.eval_congr a₂.agree hτ₁
  have e₂ := Term.eval_congr a₂.agree hτ₂
  refine chain (DEvalList.wf hdl).1 a₁ hs₁ a₂.agree hs₂ (.num ?_)
  rcases hop' with rfl | rfl
  · simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
    subst hop
    rw [if_pos rfl]
    refine hu.withTerm ?_
    simp only [Term.eval, ← e₁, ← e₂]
    exact add_term hu₁.term hu₂.term
  · simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
    subst hop
    rw [if_neg (by decide)]
    refine hu.withTerm ?_
    simp only [Term.eval, ← e₁, ← e₂]
    exact add_term hu₁.term (neg_term hu₂.term)
theorem neg_sound {e : Expr (fpy decode)} {τ : Term}
    (hdl : DEvalList decode Φ A Δ Γ (some .real) χ Ψg n₀ [e] [.num l₁ m₁ (some τ)] Ψ n₁)
    (hok : ArithOK decode (some .real) .neg [(l₁, m₁, some τ)] n₁ n₂ Ψ' l m) (hΔ : Δ.Below n₀)
    (hop : (fpy decode).arith .neg ns = some u) (hr : C.rnd (fpy decode) = some r)
    (hC : ∀ K ∈ some SCtx.real, K.Admits ι C)
    (ih : ∃ ι₁, Agree n₀ ι ι₁ ∧ Sat ι₁ Ψ ∧
      List.Forall₂ (Describes (Ψg ++ Ψ) ι₁) [.num l₁ m₁ (some τ)] (ns.map .num)) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ') ∧
      Describes (Ψg ++ (Ψ ++ Ψ')) ι' (.num l m (some (.neg τ))) (.num (r u)) := by
  obtain ⟨ι₁, a₁, hs₁, hds⟩ := ih
  obtain rfl := admits_real hC
  obtain rfl : _ = id := (Option.some.inj hr).symm
  have hτ := ((DEvalList.wf hdl).2 hΔ (ctxBelow_real _) _ (List.mem_cons_self ..)).2.2 _ rfl
  obtain ⟨u₁, rfl, hu₁⟩ := args_one hds
  obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (.cons hu₁ .nil) hop (admits_real' _) rfl
  refine chain (DEvalList.wf hdl).1 a₁ hs₁ a₂.agree hs₂ (.num ?_)
  simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
  subst hop
  refine hu.withTerm ?_
  simp only [Term.eval, ← Term.eval_congr a₂.agree hτ]
  exact neg_term hu₁.term
theorem logb_sound {e : Expr (fpy decode)} {τ : Option Term}
    (hdl : DEvalList decode Φ A Δ Γ (some .real) χ Ψg n₀ [e] [.num l₁ m₁ τ] Ψ n₁)
    (hok : ArithOK decode (some .real) .logb [(l₁, m₁, τ)] n₁ n₂ Ψ' l m) (hΔ : Δ.Below n₀)
    (hop : (fpy decode).arith .logb ns = some u) (hr : C.rnd (fpy decode) = some r)
    (hC : ∀ K ∈ some SCtx.real, K.Admits ι C)
    (ih : ∃ ι₁, Agree n₀ ι ι₁ ∧ Sat ι₁ Ψ ∧
      List.Forall₂ (Describes (Ψg ++ Ψ) ι₁) [.num l₁ m₁ τ] (ns.map .num)) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ') ∧
      Describes (Ψg ++ (Ψ ++ Ψ')) ι' (.num l m (some m₁)) (.num (r u)) := by
  obtain ⟨ι₁, a₁, hs₁, hds⟩ := ih
  obtain rfl := admits_real hC
  obtain rfl : _ = id := (Option.some.inj hr).symm
  have hm := ((DEvalList.wf hdl).2 hΔ (ctxBelow_real _) _ (List.mem_cons_self ..)).2.1
  obtain ⟨u₁, rfl, hu₁⟩ := args_one hds
  obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (.cons hu₁ .nil) hop (admits_real' _) rfl
  refine chain (DEvalList.wf hdl).1 a₁ hs₁ a₂.agree hs₂ (.num ?_)
  simp only [fpy, ArithOp.eval, Option.some.injEq] at hop
  subst hop
  refine hu.withTerm ?_
  rw [← Term.eval_congr a₂.agree hm]
  exact logb_term hu₁
theorem ext_sound {op : ArithOp} {ge : Bool} {e₁ e₂ : Expr (fpy decode)}
    (hop' : op = (if ge then .max else .min)) (hτ₁ : τ₁.Below n₂) (hτ₂ : τ₂.Below n₂)
    (hdl : DEvalList decode Φ A Δ Γ (some .real) χ Ψg n₀ [e₁, e₂]
      [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)] Ψ n₁)
    (hok : ArithOK decode (some .real) op [(l₁, m₁, some τ₁), (l₂, m₂, some τ₂)] n₁ n₂ Ψ' l m)
    (hF : Fresh n₁ n₂ Ψ') (hlb : l.Below n₂) (hmb : m.Below n₂) (hΔ : Δ.Below n₀)
    (hop : (fpy decode).arith op ns = some u) (hr : C.rnd (fpy decode) = some r)
    (hC : ∀ K ∈ some SCtx.real, K.Admits ι C)
    (ih : ∃ ι₁, Agree n₀ ι ι₁ ∧ Sat ι₁ Ψ ∧
      List.Forall₂ (Describes (Ψg ++ Ψ) ι₁) [.num l₁ m₁ (some τ₁), .num l₂ m₂ (some τ₂)]
        (ns.map .num)) :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψ ++ Ψ' ++ [Con.ext n₂ ge τ₁ τ₂ hτ₁ hτ₂]) ∧
      Describes (Ψg ++ (Ψ ++ Ψ' ++ [Con.ext n₂ ge τ₁ τ₂ hτ₁ hτ₂])) ι' (.num l m (some (.var n₂)))
        (.num (r u)) := by
  obtain ⟨ι₁, a₁, hs₁, hds⟩ := ih
  obtain rfl := admits_real hC
  obtain rfl : _ = id := (Option.some.inj hr).symm
  have hF₁ := (DEvalList.wf hdl).1
  obtain ⟨u₁, u₂, rfl, hu₁, hu₂⟩ := args_two hds
  obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (.cons hu₁ (.cons hu₂ .nil)) hop
    (admits_real' _) rfl
  have hb := (DEvalList.wf hdl).2 hΔ (ctxBelow_real _)
  have hτ₁' := (hb _ (List.mem_cons_self ..)).2.2 _ rfl
  have hτ₂' := (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2.2 _ rfl
  let z : EInt := if ge then max (τ₁.eval ι₁) (τ₂.eval ι₁) else min (τ₁.eval ι₁) (τ₂.eval ι₁)
  let ι₃ := Function.update ι₂ n₂ z
  have a₃ : Agree n₂ ι₂ ι₃ := fun x hx => (Function.update_of_ne hx.ne _ _).symm
  have f₁ : τ₁.eval ι₃ = τ₁.eval ι₁ :=
    (Term.eval_congr a₃ hτ₁).symm.trans (Term.eval_congr a₂.agree hτ₁').symm
  have f₂ : τ₂.eval ι₃ = τ₂.eval ι₁ :=
    (Term.eval_congr a₃ hτ₂).symm.trans (Term.eval_congr a₂.agree hτ₂').symm
  have hz : ι₃ n₂ = z := Function.update_self ..
  refine chain₃ hF₁ hF a₁ hs₁ a₂.agree hs₂ a₃ ?_ (.num ?_)
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    rw [Con.P_ext, f₁, f₂, hz]
    cases ge
    · exact ⟨min_le_left _ _, min_le_right _ _⟩
    · exact ⟨le_max_left _ _, le_max_right _ _⟩
  · refine (hu.congr a₃ hlb hmb (fun _ h => absurd h (by simp))).withTerm ?_
    simp only [Term.eval, hz]
    cases ge <;> simp only [Bool.false_eq_true, if_false, if_true] at hop' <;> subst hop' <;>
      simp only [fpy, ArithOp.eval, Option.some.injEq] at hop <;> subst hop
    · exact ext_term false hu₁.term hu₂.term
    · exact ext_term true hu₁.term hu₂.term
end Rules
theorem loop_sound (hA : A.Sound Φ) {e : Expr (fpy decode)} {s : Stmt (fpy decode)}
    {Δ Δᵢ Δ' : DEnv} {Γᵢ Γ' : AEnv D} {b : AVal D} {κ : Option SCtx} {χ : Option Val}
    {n₀ n₁ n₂ : ℕ} {Ψg Ψᵢ Ψ : List Con} {a : Option DVal} (hbg : Before n₀ Ψg)
    (hΔ : Δ.Below n₀) (hcov : Covers n₀ n₁ Ψg Ψᵢ s.assigned Γᵢ Δ Δᵢ) (hFᵢ : Fresh n₀ n₁ Ψᵢ)
    (hbᵢ : Δᵢ.Below n₁) (hF : Fresh n₁ n₂ Ψ) (hAx : AExec A Φ (A.refine χ e true Γᵢ) χ s Γ' b)
    (hΓ' : Γ'.Le Γᵢ) (hκ : CtxBelow n₀ κ)
    (hbody : ∀ {σ C o ι}, Exec Φ σ C s o → Sat ι (Ψg ++ Ψᵢ) → Δᵢ.Holds (Ψg ++ Ψᵢ) ι σ →
      (A.refine χ e true Γᵢ).Holds σ → (∀ K ∈ κ, K.Admits ι C) → Admits χ C →
      ∃ ι', Agree n₁ ι ι' ∧ Sat ι' Ψ ∧ Within (Ψg ++ Ψᵢ ++ Ψ) ι' Δ' a o) :
    ∀ {σ C w o ι}, Exec Φ σ C w o → w = .whileDo e s → Sat ι Ψg →
      (Δ.without s.assigned).Holds Ψg ι σ → Γᵢ.Holds σ → (∀ K ∈ κ, K.Admits ι C) → Admits χ C →
      ∃ ι', Agree n₀ ι ι' ∧ Sat ι' (Ψᵢ ++ Ψ) ∧ Within (Ψg ++ (Ψᵢ ++ Ψ)) ι' Δᵢ a o
  | _, _, _, _, ι, .whileFalse _, rfl, hsg, hU, hΓ, _, _ => by
      obtain ⟨ι₁, a₁, hs₁, hσ₁⟩ := hcov hbg ι _ hsg hΓ hU
      obtain ⟨ι₂, a₂, hs₂⟩ := Sat.extend hF ι₁
      refine ⟨ι₂, a₁.agree.trans (a₂.mono hFᵢ.le), (Sat.congr hFᵢ.before a₂ hs₁).append hs₂, ?_⟩
      simpa using hσ₁.grow (hbg.append hFᵢ) hF a₂ hbᵢ
  | _, _, _, _, ι, .whileTrue hg (.seqNormal hs hw), rfl, hsg, hU, hΓ, hC, hχ => by
      have hΓr := hA.refine hΓ hχ hg
      obtain ⟨ι₁, a₁, hs₁, hσ₁⟩ := hcov hbg ι _ hsg hΓ hU
      obtain ⟨ι₂, a₂, -, -⟩ := hbody hs ((Sat.congr hbg a₁.agree hsg).append hs₁) hσ₁ hΓr
        (admits_congr a₁.agree hκ hC) hχ
      have a₀₂ := a₁.agree.trans (a₂.mono hFᵢ.le)
      obtain ⟨ι₃, a₃, hs₃, hw'⟩ := loop_sound hA hbg hΔ hcov hFᵢ hbᵢ hF hAx hΓ' hκ hbody hw
        rfl (Sat.congr hbg a₀₂ hsg) (fun x d hd => by
          obtain ⟨v, hv, hdv⟩ := hU x d hd
          refine ⟨v, (Exec.frame _ hs rfl x (DEnv.without_eq_some.mp hd).1).trans hv, ?_⟩
          simpa using hdv.grow hbg (Fresh.nil _) a₀₂ (hΔ.without _ x d hd))
        (hΓ' _ (Fpy.exec_sound hA hs hΓr hχ hAx)) (admits_congr a₀₂ hκ hC) hχ
      exact ⟨ι₃, a₀₂.trans a₃, hs₃, hw'⟩
  | _, _, _, _, ι, .whileTrue hg (.seqRet hs), rfl, hsg, hU, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, hσ₁⟩ := hcov hbg ι _ hsg hΓ hU
      obtain ⟨ι₂, a₂, hs₂, hw⟩ := hbody hs ((Sat.congr hbg a₁.agree hsg).append hs₁) hσ₁
        (hA.refine hΓ hχ hg) (admits_congr a₁.agree hκ hC) hχ
      exact ⟨ι₂, a₁.agree.trans (a₂.mono hFᵢ.le), (Sat.congr hFᵢ.before a₂ hs₁).append hs₂,
        by simpa using hw⟩
  | _, _, _, _, _, .assign _, h, _, _, _, _, _ | _, _, _, _, _, .skip, h, _, _, _, _, _
  | _, _, _, _, _, .ret _, h, _, _, _, _, _ | _, _, _, _, _, .assert _, h, _, _, _, _, _
  | _, _, _, _, _, .seqNormal _ _, h, _, _, _, _, _ | _, _, _, _, _, .seqRet _, h, _, _, _, _, _
  | _, _, _, _, _, .iteTrue _ _, h, _, _, _, _, _ | _, _, _, _, _, .iteFalse _ _, h, _, _, _, _, _
  | _, _, _, _, _, .withCtx _ _ _, h, _, _, _, _, _ => by cases h
termination_by structural _ _ _ _ _ h => h
mutual

/-- Constraint soundness (the lemma behind Theorem 4.2), in prefix form. If
`Δ, κ ⊢♮ e : d` with fresh variables from `n₀`, `ι` satisfies the constraints
`Ψg` so far and describes the store and `κ` the context, the store lies in `Γ`
and the context in `χ`, and `⟨σ, C, e⟩ ⇓ v`, then an assignment agreeing with
`ι` below `n₀` satisfies the derivation's constraints and describes `v` by `d`. -/
theorem eval_sound (hA : A.Sound Φ) : ∀ {Δ Γ κ χ Ψg n₀ e d Ψ n₁},
    DEval decode Φ A Δ Γ κ χ Ψg n₀ e d Ψ n₁ → ∀ {σ C v ι}, Eval Φ σ C e v → Before n₀ Ψg →
      Sat ι Ψg → Δ.Below n₀ → CtxBelow n₀ κ → Δ.Holds Ψg ι σ → Γ.Holds σ →
      (∀ K ∈ κ, K.Admits ι C) → Admits χ C →
      ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ Describes (Ψg ++ Ψ) ι' d v
  | _, _, _, _, _, _, _, _, _, _, .bool, _, _, _, ι, .bool, _, _, _, _, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .bool⟩
  | _, _, _, _, _, _, _, _, _, _, .const hτ, _, _, _, ι, .num, _, _, _, _, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .num (.inr ⟨rfl, rfl, fun t ht => by
        obtain ⟨z, rfl, hz⟩ := hτ t ht
        exact hz⟩)⟩
  | _, _, _, _, _, _, _, _, _, _, .real, _, _, _, ι, .real, _, _, _, _, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .sctx rfl⟩
  | _, _, _, _, _, _, _, _, _, _, .var hΔx, _, _, _, ι, .var hx, _, _, _, _, hσ, _, _, _ => by
      obtain ⟨v', hv', hd⟩ := hσ _ _ hΔx
      refine ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, ?_⟩
      simpa [Option.some.inj (hv'.symm.trans hx)] using hd
  | _, _, _, _, _, _, _, _, _, _, .list hdl hle hF _, _, _, _, _, .list hl,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, h₁, hs₁, hds⟩ := evalList_sound hA hdl hl hbg hsg hΔ hκ hσ hΓ hC hχ
      have hF₁ := (DEvalList.wf hdl).1
      obtain ⟨hb₁, hsg₁⟩ := step hbg hsg hF₁ h₁ hs₁
      obtain ⟨ι₂, h₂, hs₂⟩ := Sat.extend hF ι₁
      exact chain hF₁ h₁ hs₁ h₂ hs₂
        (.list (by simpa using describesAll_of_le hb₁ hsg₁ h₂ hds hle))
  | _, _, _, _, _, _, _, _, _, _, .index hd₁ hd₂ hcopy hF _, _, _, _, _, .index h₁ h₂ hk,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      have hF₁ := (DEval.wf hd₁).1
      have hF₂ := (DEval.wf hd₂).1
      obtain ⟨ι₁, a₁, hs₁, hl⟩ := eval_sound hA hd₁ h₁ hbg hsg hΔ hκ hσ hΓ hC hχ
      obtain ⟨hb₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      obtain ⟨ι₂, a₂, hs₂, -⟩ := eval_sound hA hd₂ h₂ hb₁ hsg₁ (hΔ.mono hF₁.le)
        (hκ.mono hF₁.le) (hσ.grow hbg hF₁ a₁ hΔ) hΓ (admits_congr a₁ hκ hC) hχ
      obtain ⟨hb₂, hsg₂⟩ := step hb₁ hsg₁ hF₂ a₂ hs₂
      cases hl.grow hb₁ hF₂ a₂ ((DEval.wf hd₁).2 hΔ hκ) with
      | list hall =>
        obtain ⟨ι₀, h₀, hs₀, hv₀⟩ := hall.mem (List.mem_of_getElem? hk)
        obtain ⟨ι₃, a₃, hs₃, hv⟩ := hcopy hb₂ ι₂ ι₀ _ hsg₂ h₀ hs₀ hv₀
        exact chain₃ hF₁ hF₂ a₁ hs₁ a₂ hs₂ a₃.agree hs₃ (by simpa using hv)
  | _, _, _, _, _, _, _, _, _, _, .record hdf, _, _, _, _, .record hf,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, hfs⟩ := evalFields_sound hA hdf hf hbg hsg hΔ hκ hσ hΓ hC hχ
      exact ⟨ι₁, a₁, hs₁, .record hfs⟩
  | _, _, _, _, _, _, _, _, _, _, .proj hd hal, _, _, _, _, .proj h hl,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, hr⟩ := eval_sound hA hd h hbg hsg hΔ hκ hσ hΓ hC hχ
      cases hr with
      | record hfs => exact ⟨ι₁, a₁, hs₁, hfs.lookup hal hl⟩
  | _, _, _, _, _, _, _, _, _, _, .ctx (d := d) hd, _, _, _, _, .ctx h _,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, hr⟩ := eval_sound hA hd h hbg hsg hΔ hκ hσ hΓ hC hχ
      refine ⟨ι₁, a₁, hs₁, ?_⟩
      cases hc : ctxOf d with
      | none => exact .ctxv
      | some C' => exact .sctx (ctxOf_admits hr hc)
  | _, _, _, _, _, _, _, _, _, _, .arith hdl hok _ _ _, _, _, _, _, .arith hl hop hr,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, hds⟩ := evalList_sound hA hdl hl hbg hsg hΔ hκ hσ hΓ hC hχ
      obtain ⟨ι₂, a₂, hs₂, hu⟩ := hok ι₁ _ _ _ _ (numIns hds) hop (admits_congr a₁ hκ hC) hr
      exact chain (DEvalList.wf hdl).1 a₁ hs₁ a₂.agree hs₂ (.num hu)
  | _, _, _, _, _, _, _, _, _, _, .linear hop' hdl hok _ _ _, _, _, _, _, .arith hl hop hr,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ =>
      linear_sound hop' hdl hok hΔ hop hr hC (evalList_sound hA hdl hl hbg hsg hΔ hκ hσ hΓ hC hχ)
  | _, _, _, _, _, _, _, _, _, _, .neg hdl hok _ _ _, _, _, _, _, .arith hl hop hr,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ =>
      neg_sound hdl hok hΔ hop hr hC (evalList_sound hA hdl hl hbg hsg hΔ hκ hσ hΓ hC hχ)
  | _, _, _, _, _, _, _, _, _, _, .logb hdl hok _ _ _, _, _, _, _, .arith hl hop hr,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ =>
      logb_sound hdl hok hΔ hop hr hC (evalList_sound hA hdl hl hbg hsg hΔ hκ hσ hΓ hC hχ)
  | _, _, _, _, _, _, _, _, _, _, .ext hop' hτ₁ hτ₂ hdl hok hF hlb hmb, _, _, _, _,
      .arith hl hop hr, hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ =>
      ext_sound hop' hτ₁ hτ₂ hdl hok hF hlb hmb hΔ hop hr hC
        (evalList_sound hA hdl hl hbg hsg hΔ hκ hσ hΓ hC hχ)
  | _, _, _, _, _, _, _, _, _, _, .exact hdl hne, _, _, _, _, .exact hl hop,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, -⟩ := evalList_sound hA hdl hl hbg hsg hΔ hκ hσ hΓ hC hχ
      obtain ⟨b, rfl⟩ := ExactOp.eval_bool hop hne
      exact ⟨ι₁, a₁, hs₁, .bool⟩
  | _, _, _, _, _, _, _, _, _, _, .len (n₁ := n₁) hdl, _, _, _, _, .exact hl hop,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, -⟩ := evalList_sound hA hdl hl hbg hsg hΔ hκ hσ hΓ hC hχ
      have hF₁ := (DEvalList.wf hdl).1
      obtain ⟨k, rfl⟩ := ExactOp.eval_len hop
      let ι₂ := Function.update (Function.update ι₁ n₁ (lsbOf (.finite k))) (n₁ + 1)
        (msbOf (.finite k))
      have a₂ : Agree n₁ ι₁ ι₂ := fun x hx => by
        simp only [ι₂, Function.update_of_ne (show x ≠ n₁ + 1 by omega),
          Function.update_of_ne (show x ≠ n₁ by omega)]
      refine ⟨ι₂, a₁.trans (a₂.mono hF₁.le), Sat.congr hF₁.before a₂ hs₁, .num (.inr ⟨?_, ?_, ?_⟩)⟩
      · simp [ι₂, Term.eval]
      · simp [ι₂, Term.eval]
      · intro t ht; exact absurd ht (by simp)
  | _, _, _, _, _, _, _, _, _, _, .call hΦ' hd ha hbody, _, _, _, _, .call hΦ he hs,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      have ih := @exec_sound hA _ _ _ _ _ _ _ _ _ _ _ hbody
      rw [hΦ] at hΦ'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ')
      have hF₁ := (DEval.wf hd).1
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hd he hbg hsg hΔ hκ hσ hΓ hC hχ
      obtain ⟨hb₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      obtain ⟨ι₂, a₂, hs₂, d', hd', hv'⟩ := ih hs hb₁ hsg₁
        (DEnv.Below.single ((DEval.wf hd).2 hΔ hκ)) (hκ.mono hF₁.le) (DEnv.Holds.single hv)
        (AEnv.holds_single (Fpy.eval_sound hA he hΓ hχ ha)) (admits_congr a₁ hκ hC) hχ
      obtain rfl := Option.mem_some_iff.mp hd'
      exact chain hF₁ a₁ hs₁ a₂ hs₂ (by simpa using hv')
  | _, _, _, _, _, _, _, _, _, _, .int (n₁ := n₁) (a := lo) (b := hi) _ hd ha hint, _, _, _, _,
      h, hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hd h hbg hsg hΔ hκ hσ hΓ hC hχ
      have hb := (DEval.wf hd).2 hΔ hκ
      have hf := Fpy.eval_sound hA h hΓ hχ ha
      cases hv with
      | num hu =>
        obtain ⟨k, rfl, hlo, hhi⟩ := hint _ hf
        let ι₂ := Function.update ι₁ n₁ (k : EInt)
        have a₂ : Agree n₁ ι₁ ι₂ := fun x hx => (Function.update_of_ne hx.ne _ _).symm
        refine chain (DEval.wf hd).1 a₁ hs₁ a₂ (fun c hc => ?_) (.num ?_)
        · obtain rfl := List.mem_singleton.mp hc
          simpa [Con.P_between, ι₂] using ⟨hlo, hhi⟩
        · refine (hu.congr a₂ hb.1 hb.2.1 (fun _ h => absurd h (by simp))).withTerm (.inr ?_)
          simp [Term.eval, ι₂]
  | _, _, _, _, _, _, _, _, _, _, .fmt (n₁ := n₁) (lo := lo) (hi := hi) hd hl hm ha hin, _, _, _, _,
      h, hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hd h hbg hsg hΔ hκ hσ hΓ hC hχ
      have hb := (DEval.wf hd).2 hΔ hκ
      have hf := Fpy.eval_sound hA h hΓ hχ ha
      cases hv with
      | @num _ _ _ τ w hu =>
        obtain ⟨ι₂, a₂, hs₂, hw⟩ := fresh_numIn (n := n₁) (Lo := .max _ (.const lo))
          (Hi := .min _ (.const hi)) ⟨hl.mono (Nat.le_succ n₁), trivial⟩ ⟨hm, trivial⟩ ι₁ w
          fun hn => by
            obtain ⟨hl', hm'⟩ := hu.eq hn
            obtain ⟨h₁, h₂⟩ := (hin _ hf).resolve_left hn
            simp only [Term.eval, eval_update hl]
            exact ⟨le_min hm'.le h₂, max_le hl'.ge h₁⟩
        refine chain (DEval.wf hd).1 a₁ hs₁ a₂.agree hs₂ (.num ?_)
        rcases hu with hn | ⟨-, -, ht⟩
        · exact .inl hn
        · rcases hw with hn | ⟨hl₂, hm₂, -⟩
          · exact .inl hn
          · exact .inr ⟨hl₂, hm₂, fun t h' => by
              rw [ht t h', Term.eval_congr a₂.agree (hb.2.2 t h')]⟩
termination_by structural _ _ _ _ _ _ _ _ _ _ hd => hd

theorem evalList_sound (hA : A.Sound Φ) : ∀ {Δ Γ κ χ Ψg n₀ es ds Ψ n₁},
    DEvalList decode Φ A Δ Γ κ χ Ψg n₀ es ds Ψ n₁ → ∀ {σ C vs ι}, EvalList Φ σ C es vs →
      Before n₀ Ψg → Sat ι Ψg → Δ.Below n₀ → CtxBelow n₀ κ → Δ.Holds Ψg ι σ → Γ.Holds σ →
      (∀ K ∈ κ, K.Admits ι C) → Admits χ C →
      ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ List.Forall₂ (Describes (Ψg ++ Ψ) ι') ds vs
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, ι, .nil, _, _, _, _, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .nil⟩
  | _, _, _, _, _, _, _, _, _, _, .cons hd hds, _, _, _, _, .cons h hs,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      have hF₁ := (DEval.wf hd).1
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hd h hbg hsg hΔ hκ hσ hΓ hC hχ
      obtain ⟨hb₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      obtain ⟨ι₂, a₂, hs₂, hvs⟩ := evalList_sound hA hds hs hb₁ hsg₁ (hΔ.mono hF₁.le)
        (hκ.mono hF₁.le) (hσ.grow hbg hF₁ a₁ hΔ) hΓ (admits_congr a₁ hκ hC) hχ
      refine chain hF₁ a₁ hs₁ a₂ hs₂ ?_
      rw [← List.append_assoc]
      exact .cons (hv.grow hb₁ (DEvalList.wf hds).1 a₂ ((DEval.wf hd).2 hΔ hκ)) hvs
termination_by structural _ _ _ _ _ _ _ _ _ _ hd => hd

theorem evalFields_sound (hA : A.Sound Φ) : ∀ {Δ Γ κ χ Ψg n₀ fs afs Ψ n₁},
    DEvalFields decode Φ A Δ Γ κ χ Ψg n₀ fs afs Ψ n₁ → ∀ {σ C vs ι}, EvalFields Φ σ C fs vs →
      Before n₀ Ψg → Sat ι Ψg → Δ.Below n₀ → CtxBelow n₀ κ → Δ.Holds Ψg ι σ → Γ.Holds σ →
      (∀ K ∈ κ, K.Admits ι C) → Admits χ C →
      ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ DescribesFields (Ψg ++ Ψ) ι' afs vs
  | _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, ι, .nil, _, _, _, _, _, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, .nil⟩
  | _, _, _, _, _, _, _, _, _, _, .cons hd hds, _, _, _, _, .cons h hs,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      have hF₁ := (DEval.wf hd).1
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hd h hbg hsg hΔ hκ hσ hΓ hC hχ
      obtain ⟨hb₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      obtain ⟨ι₂, a₂, hs₂, hvs⟩ := evalFields_sound hA hds hs hb₁ hsg₁ (hΔ.mono hF₁.le)
        (hκ.mono hF₁.le) (hσ.grow hbg hF₁ a₁ hΔ) hΓ (admits_congr a₁ hκ hC) hχ
      refine chain hF₁ a₁ hs₁ a₂ hs₂ ?_
      rw [← List.append_assoc]
      exact .cons (hv.grow hb₁ (DEvalFields.wf hds).1 a₂ ((DEval.wf hd).2 hΔ hκ)) hvs
termination_by structural _ _ _ _ _ _ _ _ _ _ hd => hd

theorem exec_sound (hA : A.Sound Φ) : ∀ {Δ Γ κ χ Ψg n₀ s Δ' a Ψ n₁},
    DExec decode Φ A Δ Γ κ χ Ψg n₀ s Δ' a Ψ n₁ → ∀ {σ C o ι}, Exec Φ σ C s o →
      Before n₀ Ψg → Sat ι Ψg → Δ.Below n₀ → CtxBelow n₀ κ → Δ.Holds Ψg ι σ → Γ.Holds σ →
      (∀ K ∈ κ, K.Admits ι C) → Admits χ C →
      ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ Within (Ψg ++ Ψ) ι' Δ' a o
  | _, _, _, _, _, _, _, _, _, _, _, .assign hd, _, _, _, _, .assign he,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hd he hbg hsg hΔ hκ hσ hΓ hC hχ
      exact ⟨ι₁, a₁, hs₁, (hσ.grow hbg (DEval.wf hd).1 a₁ hΔ).update _ hv⟩
  | _, _, _, _, _, _, _, _, _, _, _, .skip, _, _, _, ι, .skip, _, _, _, _, hσ, _, _, _ =>
      ⟨ι, Agree.refl _ _, fun _ h => absurd h List.not_mem_nil, by simpa using hσ⟩
  | _, _, _, _, _, _, _, _, _, _, _, .ret hd, _, _, _, _, .ret he,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hd he hbg hsg hΔ hκ hσ hΓ hC hχ
      exact ⟨ι₁, a₁, hs₁, _, rfl, hv⟩
  | _, _, _, _, _, _, _, _, _, _, _, .assert hd, _, _, _, _, .assert he,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      obtain ⟨ι₁, a₁, hs₁, -⟩ := eval_sound hA hd he hbg hsg hΔ hκ hσ hΓ hC hχ
      exact ⟨ι₁, a₁, hs₁, hσ.grow hbg (DEval.wf hd).1 a₁ hΔ⟩
  | _, _, _, _, _, _, _, _, _, _, _, .seq hd₁ hAx hd₂ _ hra₂ hF _, _, _, _, _,
      .seqNormal h₁ h₂, hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      have hF₁ := (DExec.wf hd₁).1
      have hF₂ := (DExec.wf hd₂).1
      have hb₁ := (DExec.wf hd₁).2 hΔ hκ
      have hb₂ := (DExec.wf hd₂).2 hb₁.1 (hκ.mono hF₁.le)
      obtain ⟨ι₁, a₁, hs₁, hw₁⟩ := exec_sound hA hd₁ h₁ hbg hsg hΔ hκ hσ hΓ hC hχ
      obtain ⟨hp₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      obtain ⟨ι₂, a₂, hs₂, hw₂⟩ := exec_sound hA hd₂ h₂ hp₁ hsg₁ hb₁.1 (hκ.mono hF₁.le) hw₁
        (Fpy.exec_sound hA h₁ hΓ hχ hAx) (admits_congr a₁ hκ hC) hχ
      obtain ⟨hp₂, hsg₂⟩ := step hp₁ hsg₁ hF₂ a₂ hs₂
      obtain ⟨ι₃, a₃, hs₃, hw⟩ := within_seq hw₂ hp₂ hsg₂ hb₂.1 hb₂.2 hF hra₂
      exact chain₃ hF₁ hF₂ a₁ hs₁ a₂ hs₂ a₃ hs₃ (by simpa using hw)
  | _, _, _, _, _, _, _, _, _, _, _, .seq hd₁ _ hd₂ hra₁ _ hF _, _, _, _, _, .seqRet h₁,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      have hF₁ := (DExec.wf hd₁).1
      have hF₂ := (DExec.wf hd₂).1
      have hb₁ := (DExec.wf hd₁).2 hΔ hκ
      obtain ⟨ι₁, a₁, hs₁, hw₁⟩ := exec_sound hA hd₁ h₁ hbg hsg hΔ hκ hσ hΓ hC hχ
      obtain ⟨hp₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      obtain ⟨ι₂, a₂, hs₂⟩ := Sat.extend hF₂ ι₁
      obtain ⟨hp₂, hsg₂⟩ := step hp₁ hsg₁ hF₂ a₂ hs₂
      obtain ⟨ι₃, a₃, hs₃, hw⟩ := ret_join (hw₁.grow hp₁ hF₂ a₂ hb₁.1 hb₁.2) hp₂ hsg₂ hra₁
      exact chain₃ hF₁ hF₂ a₁ hs₁ a₂ hs₂ a₃ hs₃ (by simpa using hw)
  | _, _, _, _, _, _, _, _, _, _, _, .ite hd₁ hd₂ hle₁ _ hra₁ _ hF _ _, _, _, _, _,
      .iteTrue hg h₁, hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      have hF₁ := (DExec.wf hd₁).1
      have hF₂ := (DExec.wf hd₂).1
      have hb₁ := (DExec.wf hd₁).2 hΔ hκ
      obtain ⟨ι₁, a₁, hs₁, hw₁⟩ :=
        exec_sound hA hd₁ h₁ hbg hsg hΔ hκ hσ (hA.refine hΓ hχ hg) hC hχ
      obtain ⟨hp₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      obtain ⟨ι₂, a₂, hs₂⟩ := Sat.extend hF₂ ι₁
      obtain ⟨hp₂, hsg₂⟩ := step hp₁ hsg₁ hF₂ a₂ hs₂
      obtain ⟨ι₃, a₃, hs₃, hw⟩ :=
        within_join (hw₁.grow hp₁ hF₂ a₂ hb₁.1 hb₁.2) hp₂ hsg₂ hle₁ hra₁
      exact chain₃ hF₁ hF₂ a₁ hs₁ a₂ hs₂ a₃ hs₃ (by simpa using hw)
  | _, _, _, _, _, _, _, _, _, _, _, .ite hd₁ hd₂ _ hle₂ _ hra₂ hF _ _, _, _, _, ι,
      .iteFalse hg h₂, hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ => by
      have hF₁ := (DExec.wf hd₁).1
      have hF₂ := (DExec.wf hd₂).1
      obtain ⟨ι₁, a₁, hs₁⟩ := Sat.extend hF₁ ι
      obtain ⟨hp₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      obtain ⟨ι₂, a₂, hs₂, hw₂⟩ := exec_sound hA hd₂ h₂ hp₁ hsg₁ (hΔ.mono hF₁.le)
        (hκ.mono hF₁.le) (hσ.grow hbg hF₁ a₁ hΔ) (hA.refine hΓ hχ hg) (admits_congr a₁ hκ hC) hχ
      obtain ⟨hp₂, hsg₂⟩ := step hp₁ hsg₁ hF₂ a₂ hs₂
      obtain ⟨ι₃, a₃, hs₃, hw⟩ := within_join hw₂ hp₂ hsg₂ hle₂ hra₂
      exact chain₃ hF₁ hF₂ a₁ hs₁ a₂ hs₂ a₃ hs₃ (by simpa using hw)
  | _, _, _, _, _, _, _, _, _, _, _, .whileDo hcov hFᵢ hbᵢ hΓᵢ hAx hΓ' hbody, _, _, _, _, h,
      hbg, hsg, hΔ, hκ, hσ, hΓ, hC, hχ =>
      loop_sound hA hbg hΔ hcov hFᵢ hbᵢ (DExec.wf hbody).1 hAx hΓ' hκ
        (fun hE hs' hσ' hΓ'' hC' hχ' => exec_sound hA hbody hE (hbg.append hFᵢ) hs' hbᵢ
          (hκ.mono hFᵢ.le) hσ' hΓ'' hC' hχ')
        h rfl hsg (hσ.without _) (hΓᵢ _ hΓ) hC hχ
  | _, _, _, _, _, _, _, _, _, _, _, .withCtx hd ha hbody, _, _, _, _, .withCtx he _ hs,
      hbg, hsg, hΔ, _, hσ, hΓ, _, _ => by
      have hF₁ := (DEval.wf hd).1
      have hb := (DEval.wf hd).2 hΔ (ctxBelow_real _)
      obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hd he hbg hsg hΔ (ctxBelow_real _) hσ hΓ
        (admits_real' _) (admits_some _)
      obtain ⟨hp₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      have hk := knownCtx_admits (Fpy.eval_sound hA he hΓ (admits_some _) ha)
      cases hv with
      | sctx hC' =>
        obtain ⟨ι₂, a₂, hs₂, hw⟩ := exec_sound hA hbody hs hp₁ hsg₁ (hΔ.mono hF₁.le)
          (fun K hK => Option.mem_some_iff.mp hK ▸ hb) (hσ.grow hbg hF₁ a₁ hΔ) hΓ
          (fun K hK => Option.mem_some_iff.mp hK ▸ hC') hk
        exact chain hF₁ a₁ hs₁ a₂ hs₂ (by simpa using hw)
  | _, _, _, _, _, _, _, _, _, _, _, .withUnknown hd ha hbody, _, _, _, _, .withCtx he _ hs,
      hbg, hsg, hΔ, _, hσ, hΓ, _, _ => by
      have hF₁ := (DEval.wf hd).1
      obtain ⟨ι₁, a₁, hs₁, -⟩ := eval_sound hA hd he hbg hsg hΔ (ctxBelow_real _) hσ hΓ
        (admits_real' _) (admits_some _)
      obtain ⟨hp₁, hsg₁⟩ := step hbg hsg hF₁ a₁ hs₁
      have hk := knownCtx_admits (Fpy.eval_sound hA he hΓ (admits_some _) ha)
      obtain ⟨ι₂, a₂, hs₂, hw⟩ := exec_sound hA hbody hs hp₁ hsg₁ (hΔ.mono hF₁.le)
        (fun _ h => absurd h (by simp)) (hσ.grow hbg hF₁ a₁ hΔ) hΓ
        (fun _ h => absurd h (by simp)) hk
      exact chain hF₁ a₁ hs₁ a₂ hs₂ (by simpa using hw)
termination_by structural _ _ _ _ _ _ _ _ _ _ _ hd => hd

end
def Term.width (l m : Term) : Term := .add (.add m (.neg l)) (.const (1 : ℤ))
def Queried (Ψ : List Con) (m : Term) (ι : Asgn) : Prop :=
  Sat ι Ψ ∧ m.eval ι ≠ ⊥ ∧ m.eval ι ≠ ⊤
noncomputable def precBound (Ψ : List Con) (l m : Term) : EInt :=
  ⨆ (ι : Asgn) (_ : Queried Ψ m ι), (l.width m).eval ι
noncomputable def lsbBound (Ψ : List Con) (l m : Term) : EInt :=
  ⨅ (ι : Asgn) (_ : Queried Ψ m ι), l.eval ι
noncomputable def msbBound (Ψ : List Con) (m : Term) : EInt :=
  ⨆ (ι : Asgn) (_ : Queried Ψ m ι), m.eval ι
section Format
variable {Ψ : List Con} {ι : Asgn} {l m : Term} {τ : Option Term} {x : ℝ}
end Format
end Fpy.DigitBound


