-- Prove2me | Definitions.Def_Fpy_Semantics
-- name    : Fpy_Semantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:38:01.797059+00:00
-- url     : https://prove2.me/theorems/a511aa2b-2acc-443e-a340-79e430c95055
-- title:
--   Semantics
-- statement:
--   Definitions and structural lemmas for Semantics, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Semantics.lean

import Definitions.Def_Fpy_Syntax
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
namespace Fpy
variable {L : Signature}
abbrev Store := Var → Option Val
def Store.single (y : Var) (v : Val) : Store := fun x => if x = y then some v else none
def Store.update (σ : Store) (x : Var) (v : Val) : Store := Function.update σ x (some v)
inductive Outcome where
  | normal (σ : Store)
  | ret (v : Val)
def Val.rnd (L : Signature) : Val → Option (Num → Num)
  | .real => some id
  | .ctx fs => L.ρ fs
  | _ => none
variable (Φ : Program L)
mutual

inductive Eval : Store → Val → Expr L → Val → Prop
  | bool {σ C b} : Eval σ C (.bool b) (.bool b)
  | num {σ C n} : Eval σ C (.num n) (.num n)
  | real {σ C} : Eval σ C .real .real
  | var {σ C x v} : σ x = some v → Eval σ C (.var x) v
  | list {σ C es vs} : EvalList σ C es vs → Eval σ C (.list es) (.list vs)
  | index {σ C e₁ e₂ vs v} {k : ℕ} :
      Eval σ C e₁ (.list vs) → Eval σ C e₂ (.num (.finite k)) → vs[k]? = some v →
      Eval σ C (.index e₁ e₂) v
  | record {σ C fs vs} : EvalFields σ C fs vs → Eval σ C (.record fs) (.record vs)
  | proj {σ C e fs l v} : Eval σ C e (.record fs) → fs.lookup l = some v →
      Eval σ C (.proj e l) v
  | ctx {σ C e fs} : Eval σ C e (.record fs) → (L.ρ fs).isSome →
      Eval σ C (.ctx e) (.ctx fs)
  | arith {σ C op es ns n r} : EvalList σ C es (ns.map .num) → L.arith op ns = some n →
      C.rnd L = some r → Eval σ C (.arith op es) (.num (r n))
  | exact {σ C op es vs v} : EvalList σ C es vs → L.exact op vs = some v →
      Eval σ C (.exact op es) v
  | call {σ C f e y s v v'} : Φ f = some (y, s) → Eval σ C e v →
      Exec (.single y v) C s (.ret v') → Eval σ C (.call f e) v'

inductive EvalList : Store → Val → List (Expr L) → List Val → Prop
  | nil {σ C} : EvalList σ C [] []
  | cons {σ C e es v vs} : Eval σ C e v → EvalList σ C es vs → EvalList σ C (e :: es) (v :: vs)

inductive EvalFields : Store → Val → List (Label × Expr L) → List (Label × Val) → Prop
  | nil {σ C} : EvalFields σ C [] []
  | cons {σ C l e fs v vs} : Eval σ C e v → EvalFields σ C fs vs →
      EvalFields σ C ((l, e) :: fs) ((l, v) :: vs)

inductive Exec : Store → Val → Stmt L → Outcome → Prop
  | assign {σ C x e v} : Eval σ C e v → Exec σ C (.assign x e) (.normal (σ.update x v))
  | skip {σ C} : Exec σ C .skip (.normal σ)
  | ret {σ C e v} : Eval σ C e v → Exec σ C (.ret e) (.ret v)
  | assert {σ C e} : Eval σ C e (.bool true) → Exec σ C (.assert e) (.normal σ)
  | seqNormal {σ C s₁ s₂ σ' o} : Exec σ C s₁ (.normal σ') → Exec σ' C s₂ o →
      Exec σ C (.seq s₁ s₂) o
  | seqRet {σ C s₁ s₂ v} : Exec σ C s₁ (.ret v) → Exec σ C (.seq s₁ s₂) (.ret v)
  | iteTrue {σ C e s₁ s₂ o} : Eval σ C e (.bool true) → Exec σ C s₁ o →
      Exec σ C (.ite e s₁ s₂) o
  | iteFalse {σ C e s₁ s₂ o} : Eval σ C e (.bool false) → Exec σ C s₂ o →
      Exec σ C (.ite e s₁ s₂) o
  | whileFalse {σ C e s} : Eval σ C e (.bool false) → Exec σ C (.whileDo e s) (.normal σ)
  | whileTrue {σ C e s o} : Eval σ C e (.bool true) → Exec σ C (.seq s (.whileDo e s)) o →
      Exec σ C (.whileDo e s) o
  | withCtx {σ C e C' s o} : Eval σ .real e C' → C'.IsCtx → Exec σ C' s o →
      Exec σ C (.withCtx e s) o

end
mutual

theorem Eval.det {σ : Store} {C : Val} {e : Expr L} {v v' : Val} :
    Eval Φ σ C e v → Eval Φ σ C e v' → v = v'
  | .bool, .bool | .num, .num | .real, .real => rfl
  | .var h, .var h' => Option.some.inj (h.symm.trans h')
  | .list h, .list h' => by rw [EvalList.det h h']
  | .index h₁ h₂ hk, .index h₁' h₂' hk' => by
      obtain rfl := Val.list.inj (Eval.det h₁ h₁')
      have hk₀ := Eval.det h₂ h₂'
      simp only [Val.num.injEq, Mpfx.WithSpecial.finite.injEq, Nat.cast_inj] at hk₀
      subst hk₀
      exact Option.some.inj (hk.symm.trans hk')
  | .record h, .record h' => by rw [EvalFields.det h h']
  | .proj h hl, .proj h' hl' => by
      obtain rfl := Val.record.inj (Eval.det h h')
      exact Option.some.inj (hl.symm.trans hl')
  | .ctx h _, .ctx h' _ => by rw [Val.record.inj (Eval.det h h')]
  | .arith hl hop hr, .arith hl' hop' hr' => by
      obtain rfl := List.map_injective_iff.mpr (fun _ _ h => Val.num.inj h) (EvalList.det hl hl')
      obtain rfl := Option.some.inj (hop.symm.trans hop')
      obtain rfl := Option.some.inj (hr.symm.trans hr')
      rfl
  | .exact hl hop, .exact hl' hop' => by
      obtain rfl := EvalList.det hl hl'
      exact Option.some.inj (hop.symm.trans hop')
  | .call hΦ he hs, .call hΦ' he' hs' => by
      rw [hΦ] at hΦ'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hΦ')
      obtain rfl := Eval.det he he'
      exact Outcome.ret.inj (Exec.det hs hs')
termination_by structural h _ => h

theorem EvalList.det {σ : Store} {C : Val} {es : List (Expr L)} {vs vs' : List Val} :
    EvalList Φ σ C es vs → EvalList Φ σ C es vs' → vs = vs'
  | .nil, .nil => rfl
  | .cons h hs, .cons h' hs' => by rw [Eval.det h h', EvalList.det hs hs']
termination_by structural h _ => h

theorem EvalFields.det {σ : Store} {C : Val} {fs : List (Label × Expr L)}
    {vs vs' : List (Label × Val)} : EvalFields Φ σ C fs vs → EvalFields Φ σ C fs vs' → vs = vs'
  | .nil, .nil => rfl
  | .cons h hs, .cons h' hs' => by rw [Eval.det h h', EvalFields.det hs hs']
termination_by structural h _ => h

theorem Exec.det {σ : Store} {C : Val} {s : Stmt L} {o o' : Outcome} :
    Exec Φ σ C s o → Exec Φ σ C s o' → o = o'
  | .assign he, .assign he' | .ret he, .ret he' => by rw [Eval.det he he']
  | .skip, .skip | .assert _, .assert _ | .whileFalse _, .whileFalse _ => rfl
  | .seqNormal h₁ h₂, .seqNormal h₁' h₂' => by
      obtain rfl := Outcome.normal.inj (Exec.det h₁ h₁')
      exact Exec.det h₂ h₂'
  | .seqNormal h₁ _, .seqRet h₁' | .seqRet h₁, .seqNormal h₁' _ => by cases Exec.det h₁ h₁'
  | .seqRet h₁, .seqRet h₁' => Exec.det h₁ h₁'
  | .iteTrue _ h, .iteTrue _ h' | .iteFalse _ h, .iteFalse _ h' => Exec.det h h'
  | .iteTrue he _, .iteFalse he' _ | .iteFalse he _, .iteTrue he' _
  | .whileFalse he, .whileTrue he' _ | .whileTrue he _, .whileFalse he' => by
      cases Eval.det he he'
  | .whileTrue _ h, .whileTrue _ h' => Exec.det h h'
  | .withCtx he _ hs, .withCtx he' _ hs' => by
      obtain rfl := Eval.det he he'
      exact Exec.det hs hs'
termination_by structural h _ => h

end
def Stmt.assigned : Stmt L → List Var
  | .assign x _ => [x]
  | .seq s₁ s₂ | .ite _ s₁ s₂ => s₁.assigned ++ s₂.assigned
  | .whileDo _ s | .withCtx _ s => s.assigned
  | .ret _ | .assert _ | .skip => []
def Run (f : Fn) (v v' : Val) : Prop :=
  ∃ y s, Φ f = some (y, s) ∧ Exec Φ (.single y v) .real s (.ret v')
end Fpy


