-- Prove2me | Definitions.Def_Fpy_DigitBound_Reach
-- name    : Fpy_DigitBound_Reach
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:42:53.063646+00:00
-- url     : https://prove2.me/theorems/86534eff-aa6f-41ea-b870-343b29ecbc03
-- title:
--   Reach
-- statement:
--   Definitions and structural lemmas for Reach, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Reach.lean

import Definitions.Def_Fpy_DigitBound_Sound
import Theorems.Thm_Fpy_DigitBound_AgreeOut_agree
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_grow
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_single
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_without
import Theorems.Thm_Fpy_DigitBound_EInt_top_add_coe
import Theorems.Thm_Fpy_DigitBound_LsbAt_le
import Theorems.Thm_Fpy_DigitBound_Within_grow
import Theorems.Thm_Fpy_DigitBound_admits_congr
import Theorems.Thm_Fpy_DigitBound_lsbOf_abs
import Theorems.Thm_Fpy_DigitBound_lsbOf_neg
import Theorems.Thm_Fpy_DigitBound_msbOf_abs
import Theorems.Thm_Fpy_DigitBound_msbOf_neg
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
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
structure Ready (Δ : DEnv) (Γ : AEnv D) (κ : Option SCtx) (χ : Option Val) (Ψg : List Con)
    (n₀ : ℕ) (σ : Store) (C : Val) (ι : Asgn) : Prop where
  before : Before n₀ Ψg
  sat : Sat ι Ψg
  below : Δ.Below n₀
  ctxBelow : CtxBelow n₀ κ
  holds : Δ.Holds Ψg ι σ
  fmt : Γ.Holds σ
  ctx : ∀ K ∈ κ, K.Admits ι C
  admits : Admits χ C
variable (decode D) in
/-- An expression with its judgment `Δ, κ ⊢♮ e : d`, store and context. -/
structure Site where
  Δ : DEnv
  Γ : AEnv D
  κ : Option SCtx
  χ : Option Val
  Ψg : List Con
  n₀ : ℕ
  e : Expr (fpy decode)
  d : DVal
  Ψ : List Con
  n₁ : ℕ
  σ : Store
  C : Val
inductive Iter (Φ : Program (fpy decode)) (C : Val) (e : Expr (fpy decode))
    (s : Stmt (fpy decode)) : Store → Store → Prop
  | refl {σ} : Iter Φ C e s σ σ
  | step {σ σ₁ σ₂} : Eval Φ σ C e (.bool true) → Exec Φ σ C s (.normal σ₁) →
      Iter Φ C e s σ₁ σ₂ → Iter Φ C e s σ σ₂
variable (decode Φ A) (t : Site decode D)
mutual

/-- Analyzing `e` by `J` from `σ` under `C` visits `t`. -/
inductive EReach : DEnv → AEnv D → Option SCtx → Option Val → List Con → ℕ →
    Expr (fpy decode) → DVal → List Con → ℕ → Store → Val → Prop
  | here : DEval decode Φ A t.Δ t.Γ t.κ t.χ t.Ψg t.n₀ t.e t.d t.Ψ t.n₁ →
      EReach t.Δ t.Γ t.κ t.χ t.Ψg t.n₀ t.e t.d t.Ψ t.n₁ t.σ t.C
  /-- A subexpression, after its earlier siblings' constraints `Ψpre`. -/
  | inner {Δ Γ κ χ Ψg n₀ Ψpre n e' d' Ψe ne Ψpost n₁ e d σ C} : Fresh n₀ n Ψpre →
      EReach Δ Γ κ χ (Ψg ++ Ψpre) n e' d' Ψe ne σ C → Fresh ne n₁ Ψpost →
      EReach Δ Γ κ χ Ψg n₀ e d (Ψpre ++ Ψe ++ Ψpost) n₁ σ C
  /-- The callee's body, from the argument's value. -/
  | call {Δ Γ κ χ Ψg n₀ f e y s d a Ψ n₁ v Δ' a' Ψ' n₂ d' σ C} : Φ f = some (y, s) →
      DEval decode Φ A Δ Γ κ χ Ψg n₀ e d Ψ n₁ → AEval A Φ Γ χ e a → Eval Φ σ C e v →
      SReach (.single y d) (.single y a) κ χ (Ψg ++ Ψ) n₁ s Δ' a' Ψ' n₂ (.single y v) C →
      EReach Δ Γ κ χ Ψg n₀ (.call f e) d' (Ψ ++ Ψ') n₂ σ C

/-- Analyzing `s` by `J` and running it from `σ` under `C` visits `t`. -/
inductive SReach : DEnv → AEnv D → Option SCtx → Option Val → List Con → ℕ →
    Stmt (fpy decode) → DEnv → Option DVal → List Con → ℕ → Store → Val → Prop
  /-- An expression of `s` under its context. -/
  | expr {Δ Γ κ χ Ψg n₀ Ψpre n e d Ψe ne Ψpost n₁ s Δ' a σ C} : Fresh n₀ n Ψpre →
      EReach Δ Γ κ χ (Ψg ++ Ψpre) n e d Ψe ne σ C → Fresh ne n₁ Ψpost →
      SReach Δ Γ κ χ Ψg n₀ s Δ' a (Ψpre ++ Ψe ++ Ψpost) n₁ σ C
  /-- `s₁` of `s₁; s₂`. -/
  | first {Δ Γ κ χ Ψg n₀ s₁ Δ₁ a₁ Ψ₁ n₁ Ψ' n₂ s Δ' a σ C} :
      SReach Δ Γ κ χ Ψg n₀ s₁ Δ₁ a₁ Ψ₁ n₁ σ C → Fresh n₁ n₂ Ψ' →
      SReach Δ Γ κ χ Ψg n₀ s Δ' a (Ψ₁ ++ Ψ') n₂ σ C
  /-- `s₂` of `s₁; s₂`, from where `s₁` ended. -/
  | after {Δ Γ κ χ Ψg n₀ s₁ Δ₁ a₁ Ψ₁ n₁ Γ₁ b₁ σ₁ s₂ Δ₂ a₂ Ψ₂ n₂ Ψ' n₃ s Δ' a σ C} :
      DExec decode Φ A Δ Γ κ χ Ψg n₀ s₁ Δ₁ a₁ Ψ₁ n₁ → AExec A Φ Γ χ s₁ Γ₁ b₁ →
      Exec Φ σ C s₁ (.normal σ₁) →
      SReach Δ₁ Γ₁ κ χ (Ψg ++ Ψ₁) n₁ s₂ Δ₂ a₂ Ψ₂ n₂ σ₁ C → Fresh n₂ n₃ Ψ' →
      SReach Δ Γ κ χ Ψg n₀ s Δ' a (Ψ₁ ++ Ψ₂ ++ Ψ') n₃ σ C
  /-- A branch of `if e`, where `e` is `b`. -/
  | branch {Δ Γ κ χ Ψg n₀ Ψpre n e b s' Δs as Ψs ns Ψpost n₁ s Δ' a σ C} :
      Fresh n₀ n Ψpre → Eval Φ σ C e (.bool b) →
      SReach Δ (A.refine χ e b Γ) κ χ (Ψg ++ Ψpre) n s' Δs as Ψs ns σ C → Fresh ns n₁ Ψpost →
      SReach Δ Γ κ χ Ψg n₀ s Δ' a (Ψpre ++ Ψs ++ Ψpost) n₁ σ C
  /-- The body of `while e do s`, after any number of iterations (D-While). -/
  | loop {Δ Γ κ χ Ψg n₀ e s Δᵢ Ψᵢ n₁ Γᵢ Γ' b Δ' a Ψ n₂ σ σ' C} :
      Covers n₀ n₁ Ψg Ψᵢ s.assigned Γᵢ Δ Δᵢ → Fresh n₀ n₁ Ψᵢ → Δᵢ.Below n₁ → Γ.Le Γᵢ →
      AExec A Φ (A.refine χ e true Γᵢ) χ s Γ' b → Γ'.Le Γᵢ → Iter Φ C e s σ σ' →
      Eval Φ σ' C e (.bool true) →
      SReach Δᵢ (A.refine χ e true Γᵢ) κ χ (Ψg ++ Ψᵢ) n₁ s Δ' a Ψ n₂ σ' C →
      SReach Δ Γ κ χ Ψg n₀ (.whileDo e s) Δᵢ a (Ψᵢ ++ Ψ) n₂ σ C
  /-- The context expression of `with e in s`, under `R`. -/
  | ctxExpr {Δ Γ κ χ Ψg n₀ e d Ψe ne Ψpost n₁ s Δ' a σ C} :
      EReach Δ Γ (some .real) (some .real) Ψg n₀ e d Ψe ne σ .real → Fresh ne n₁ Ψpost →
      SReach Δ Γ κ χ Ψg n₀ s Δ' a (Ψe ++ Ψpost) n₁ σ C
  /-- The body of `with e in s` under a known context (D-Context). -/
  | ctx {Δ Γ κ χ Ψg n₀ e K Ψ n₁ a₀ C' s Δ' a Ψ' n₂ w Δw aw σ C} :
      DEval decode Φ A Δ Γ (some .real) (some .real) Ψg n₀ e (.ctx K) Ψ n₁ →
      AEval A Φ Γ (some .real) e a₀ → Eval Φ σ .real e C' →
      SReach Δ Γ (some K) (knownCtx a₀) (Ψg ++ Ψ) n₁ s Δ' a Ψ' n₂ σ C' →
      SReach Δ Γ κ χ Ψg n₀ w Δw aw (Ψ ++ Ψ') n₂ σ C
  /-- The body of `with e in s` under an unknown context. -/
  | unknown {Δ Γ κ χ Ψg n₀ e d Ψ n₁ a₀ C' s Δ' a Ψ' n₂ w Δw aw σ C} :
      DEval decode Φ A Δ Γ (some .real) (some .real) Ψg n₀ e d Ψ n₁ →
      AEval A Φ Γ (some .real) e a₀ → Eval Φ σ .real e C' →
      SReach Δ Γ none (knownCtx a₀) (Ψg ++ Ψ) n₁ s Δ' a Ψ' n₂ σ C' →
      SReach Δ Γ κ χ Ψg n₀ w Δw aw (Ψ ++ Ψ') n₂ σ C

end
variable {decode Φ A t}
def Tail (Ψg' Ψ' : List Con) (n' : ℕ) (Ψ : List Con) (n : ℕ) : Prop :=
  ∃ Ψr, Ψ = Ψg' ++ Ψ' ++ Ψr ∧ Fresh n' n Ψr
theorem Tail.append {Ψg' Ψ' Ψ Ψ₂ : List Con} {n' n n₂ : ℕ} (h : Tail Ψg' Ψ' n' Ψ n)
    (hF : Fresh n n₂ Ψ₂) : Tail Ψg' Ψ' n' (Ψ ++ Ψ₂) n₂ :=
  let ⟨Ψr, he, hr⟩ := h
  ⟨Ψr ++ Ψ₂, by rw [he]; simp, hr.append hF⟩
def Visit (t : Site decode D) (Ψ : List Con) (n : ℕ) : Prop :=
  DEval decode Φ A t.Δ t.Γ t.κ t.χ t.Ψg t.n₀ t.e t.d t.Ψ t.n₁ ∧
    (∃ ι, Ready t.Δ t.Γ t.κ t.χ t.Ψg t.n₀ t.σ t.C ι) ∧ Tail t.Ψg t.Ψ t.n₁ Ψ n
section Ready
variable {Δ : DEnv} {Γ : AEnv D} {κ : Option SCtx} {χ : Option Val} {Ψg : List Con} {n₀ : ℕ}
  {σ : Store} {C : Val} {ι : Asgn}
theorem Ready.skip {n : ℕ} {Ψ : List Con} (h : Ready Δ Γ κ χ Ψg n₀ σ C ι) (hF : Fresh n₀ n Ψ) :
    ∃ ι', Ready Δ Γ κ χ (Ψg ++ Ψ) n σ C ι' :=
  let ⟨ι', a, hs⟩ := Sat.extend hF ι
  ⟨ι', h.before.append hF, (Sat.congr h.before a h.sat).append hs, h.below.mono hF.le,
    h.ctxBelow.mono hF.le, h.holds.grow h.before hF a h.below, h.fmt,
    admits_congr a h.ctxBelow h.ctx, h.admits⟩
theorem Ready.refine (hA : A.Sound Φ) {e : Expr (fpy decode)} {b : Bool}
    (h : Ready Δ Γ κ χ Ψg n₀ σ C ι) (hg : Eval Φ σ C e (.bool b)) :
    Ready Δ (A.refine χ e b Γ) κ χ Ψg n₀ σ C ι :=
  { h with fmt := hA.refine h.fmt h.admits hg }
theorem Ready.exec (hA : A.Sound Φ) {s : Stmt (fpy decode)} {Δ₁ : DEnv} {a : Option DVal}
    {Ψ : List Con} {n₁ : ℕ} {Γ₁ : AEnv D} {b : AVal D} {σ₁ : Store}
    (h : Ready Δ Γ κ χ Ψg n₀ σ C ι) (hd : DExec decode Φ A Δ Γ κ χ Ψg n₀ s Δ₁ a Ψ n₁)
    (hAx : AExec A Φ Γ χ s Γ₁ b) (hE : Exec Φ σ C s (.normal σ₁)) :
    ∃ ι', Ready Δ₁ Γ₁ κ χ (Ψg ++ Ψ) n₁ σ₁ C ι' := by
  have hF := (DExec.wf hd).1
  obtain ⟨ι', a', hs, hw⟩ := exec_sound hA hd hE h.before h.sat h.below h.ctxBelow h.holds h.fmt
    h.ctx h.admits
  exact ⟨ι', h.before.append hF, (step h.before h.sat hF a' hs).2,
    ((DExec.wf hd).2 h.below h.ctxBelow).1, h.ctxBelow.mono hF.le, hw,
    Fpy.exec_sound hA hE h.fmt h.admits hAx, admits_congr a' h.ctxBelow h.ctx, h.admits⟩
end Ready
theorem Iter.holds (hA : A.Sound Φ) {C : Val} {e : Expr (fpy decode)} {s : Stmt (fpy decode)}
    {Γᵢ Γ' : AEnv D} {χ : Option Val} {b : AVal D} {Δ : DEnv} {Ψg : List Con} {ι : Asgn}
    (hAx : AExec A Φ (A.refine χ e true Γᵢ) χ s Γ' b) (hΓ' : Γ'.Le Γᵢ) (hχ : Admits χ C) :
    ∀ {σ σ' : Store}, Iter Φ C e s σ σ' → Γᵢ.Holds σ → (Δ.without s.assigned).Holds Ψg ι σ →
      Γᵢ.Holds σ' ∧ (Δ.without s.assigned).Holds Ψg ι σ'
  | _, _, .refl, hΓ, hU => ⟨hΓ, hU⟩
  | _, _, .step hg hs hit, hΓ, hU =>
    Iter.holds hA hAx hΓ' hχ hit (hΓ' _ (Fpy.exec_sound hA hs (hA.refine hΓ hχ hg) hχ hAx))
      fun x d hd =>
        let ⟨v, hv, hdv⟩ := hU x d hd
        ⟨v, (Exec.frame _ hs rfl x (DEnv.without_eq_some.mp hd).1).trans hv, hdv⟩
mutual

/-- A site visited by an expression meets Theorem 4.2's hypotheses. -/
theorem EReach.sound (hA : A.Sound Φ) : ∀ {Δ Γ κ χ Ψg n₀ e d Ψ n₁ σ C},
    EReach decode Φ A t Δ Γ κ χ Ψg n₀ e d Ψ n₁ σ C → ∀ {ι}, Ready Δ Γ κ χ Ψg n₀ σ C ι →
      Visit (Φ := Φ) (A := A) t (Ψg ++ Ψ) n₁
  | _, _, _, _, _, _, _, _, _, _, _, _, .here hd, ι, h =>
    ⟨hd, ⟨ι, h⟩, [], by simp, Fresh.nil _⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, .inner hF₁ hr hF₂, _, h => by
    obtain ⟨_, h₁⟩ := h.skip hF₁
    obtain ⟨hd, hι, ht⟩ := EReach.sound hA hr h₁
    exact ⟨hd, hι, by simpa only [List.append_assoc] using ht.append hF₂⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, .call _ hde ha hev hr, _, h => by
    have hF := (DEval.wf hde).1
    obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hde hev h.before h.sat h.below h.ctxBelow
      h.holds h.fmt h.ctx h.admits
    obtain ⟨hd, hι, ht⟩ := SReach.sound hA hr ⟨h.before.append hF,
      (step h.before h.sat hF a₁ hs₁).2, DEnv.Below.single ((DEval.wf hde).2 h.below h.ctxBelow),
      h.ctxBelow.mono hF.le, DEnv.Holds.single hv,
      AEnv.holds_single (Fpy.eval_sound hA hev h.fmt h.admits ha),
      admits_congr a₁ h.ctxBelow h.ctx, h.admits⟩
    exact ⟨hd, hι, by simpa only [List.append_assoc] using ht⟩

/-- A site visited by a statement meets Theorem 4.2's hypotheses. -/
theorem SReach.sound (hA : A.Sound Φ) : ∀ {Δ Γ κ χ Ψg n₀ s Δ' a Ψ n₁ σ C},
    SReach decode Φ A t Δ Γ κ χ Ψg n₀ s Δ' a Ψ n₁ σ C → ∀ {ι}, Ready Δ Γ κ χ Ψg n₀ σ C ι →
      Visit (Φ := Φ) (A := A) t (Ψg ++ Ψ) n₁
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .expr hF₁ hr hF₂, _, h => by
    obtain ⟨_, h₁⟩ := h.skip hF₁
    obtain ⟨hd, hι, ht⟩ := EReach.sound hA hr h₁
    exact ⟨hd, hι, by simpa only [List.append_assoc] using ht.append hF₂⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .first hr hF, _, h => by
    obtain ⟨hd, hι, ht⟩ := SReach.sound hA hr h
    exact ⟨hd, hι, by simpa only [List.append_assoc] using ht.append hF⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .after hd₁ hAx hE hr hF, _, h => by
    obtain ⟨_, h₁⟩ := h.exec hA hd₁ hAx hE
    obtain ⟨hd, hι, ht⟩ := SReach.sound hA hr h₁
    exact ⟨hd, hι, by simpa only [List.append_assoc] using ht.append hF⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .branch hF₁ hg hr hF₂, _, h => by
    obtain ⟨_, h₁⟩ := (h.refine hA hg).skip hF₁
    obtain ⟨hd, hι, ht⟩ := SReach.sound hA hr h₁
    exact ⟨hd, hι, by simpa only [List.append_assoc] using ht.append hF₂⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .loop hcov hFᵢ hbᵢ hΓᵢ hAx hΓ' hit hg hr, ι, h => by
    obtain ⟨hΓk, hUk⟩ := hit.holds hA hAx hΓ' h.admits (hΓᵢ _ h.fmt) (h.holds.without _)
    obtain ⟨ι₁, a₁, hs₁, hσ₁⟩ := hcov h.before ι _ h.sat hΓk hUk
    obtain ⟨hd, hι, ht⟩ := SReach.sound hA hr ⟨h.before.append hFᵢ,
      (Sat.congr h.before a₁.agree h.sat).append hs₁, hbᵢ, h.ctxBelow.mono hFᵢ.le, hσ₁,
      hA.refine hΓk h.admits hg, admits_congr a₁.agree h.ctxBelow h.ctx, h.admits⟩
    exact ⟨hd, hι, by simpa only [List.append_assoc] using ht⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .ctxExpr hr hF, _, h => by
    obtain ⟨hd, hι, ht⟩ := EReach.sound hA hr ⟨h.before, h.sat, h.below, ctxBelow_real _,
      h.holds, h.fmt, admits_real' _, admits_some _⟩
    exact ⟨hd, hι, by simpa only [List.append_assoc] using ht.append hF⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .ctx hde ha hev hr, _, h => by
    have hF := (DEval.wf hde).1
    have hb := (DEval.wf hde).2 h.below (ctxBelow_real _)
    obtain ⟨ι₁, a₁, hs₁, hv⟩ := eval_sound hA hde hev h.before h.sat h.below (ctxBelow_real _)
      h.holds h.fmt (admits_real' _) (admits_some _)
    cases hv with
    | sctx hC' =>
      obtain ⟨hd, hι, ht⟩ := SReach.sound hA hr ⟨h.before.append hF,
        (step h.before h.sat hF a₁ hs₁).2, h.below.mono hF.le,
        fun K hK => Option.mem_some_iff.mp hK ▸ hb, h.holds.grow h.before hF a₁ h.below, h.fmt,
        fun K hK => Option.mem_some_iff.mp hK ▸ hC',
        knownCtx_admits (Fpy.eval_sound hA hev h.fmt (admits_some _) ha)⟩
      exact ⟨hd, hι, by simpa only [List.append_assoc] using ht⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .unknown hde ha hev hr, _, h => by
    have hF := (DEval.wf hde).1
    obtain ⟨ι₁, a₁, hs₁, -⟩ := eval_sound hA hde hev h.before h.sat h.below (ctxBelow_real _)
      h.holds h.fmt (admits_real' _) (admits_some _)
    obtain ⟨hd, hι, ht⟩ := SReach.sound hA hr ⟨h.before.append hF,
      (step h.before h.sat hF a₁ hs₁).2, h.below.mono hF.le, fun _ h => absurd h (by simp),
      h.holds.grow h.before hF a₁ h.below, h.fmt, fun _ h => absurd h (by simp),
      knownCtx_admits (Fpy.eval_sound hA hev h.fmt (admits_some _) ha)⟩
    exact ⟨hd, hι, by simpa only [List.append_assoc] using ht⟩

end
end Fpy.DigitBound


