-- Prove2me | Definitions.Def_Fpy_FormatInference_Defs
-- name    : Fpy_FormatInference_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T05:39:08.121761+00:00
-- url     : https://prove2.me/theorems/ed18ac4f-1c4f-4ca8-a164-7285cda46768
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Defs.lean

import Definitions.Def_Fpy_Semantics
set_option autoImplicit true
namespace Fpy
structure FormatDomain where
  Fmt : Type
  /-- The values a format contains. -/
  γ : Fmt → Set Num
  top : Fmt
  bot : Fmt
  join : Fmt → Fmt → Fmt
  /-- A containment check. -/
  sub : Fmt → Fmt → Bool
  /-- A format containing a constant. -/
  ofNum : Num → Fmt
  mem_top : ∀ n, n ∈ γ top
  mem_join_left : ∀ {F₁ F₂ n}, n ∈ γ F₁ → n ∈ γ (join F₁ F₂)
  mem_join_right : ∀ {F₁ F₂ n}, n ∈ γ F₂ → n ∈ γ (join F₁ F₂)
  sub_sound : ∀ {F₁ F₂}, sub F₁ F₂ = true → γ F₁ ⊆ γ F₂
  mem_ofNum : ∀ n, n ∈ γ (ofNum n)
variable {L : Signature} {D : FormatDomain}
variable (D) in
/-- Abstract values: a format bounds a number, `list a` bounds every element by
`a`, records are bounded field by field, `other` (`•`) is any boolean or
context, `known C` is exactly the context `C`, and `top` is any value. -/
inductive AVal where
  | fmt (F : D.Fmt)
  | list (a : AVal)
  | record (fs : List (Label × AVal))
  | other
  | known (C : Val)
  | top
mutual

/-- `Describes a v` is `v ∈ γ(a)`. -/
inductive Describes : AVal D → Val → Prop
  | fmt {F n} : n ∈ D.γ F → Describes (.fmt F) (.num n)
  | list {a vs} : DescribesAll a vs → Describes (.list a) (.list vs)
  | record {afs fs} : DescribesFields afs fs → Describes (.record afs) (.record fs)
  | bool {b} : Describes .other (.bool b)
  | real : Describes .other .real
  | ctx {fs} : Describes .other (.ctx fs)
  | known {C} : Describes (.known C) C
  | top {v} : Describes .top v

/-- `a` describes every element of a list. -/
inductive DescribesAll : AVal D → List Val → Prop
  | nil {a} : DescribesAll a []
  | cons {a v vs} : Describes a v → DescribesAll a vs → DescribesAll a (v :: vs)

/-- Records with the same labels in order, described field by field. -/
inductive DescribesFields : List (Label × AVal D) → List (Label × Val) → Prop
  | nil : DescribesFields [] []
  | cons {l a v afs fs} : Describes a v → DescribesFields afs fs →
      DescribesFields ((l, a) :: afs) ((l, v) :: fs)

end
open Classical in
mutual

/-- The join of abstract values. Mismatched shapes give `top`. -/
noncomputable def AVal.join : AVal D → AVal D → AVal D
  | .fmt F₁, .fmt F₂ => .fmt (D.join F₁ F₂)
  | .list a₁, .list a₂ => .list (a₁.join a₂)
  | .record fs₁, .record fs₂ => (AVal.joinFields fs₁ fs₂).elim .top .record
  | .other, .other => .other
  | .known C₁, .known C₂ => if C₁ = C₂ then .known C₁ else .top
  | _, _ => .top

/-- Field-by-field join of two records with the same labels in order. -/
noncomputable def AVal.joinFields :
    List (Label × AVal D) → List (Label × AVal D) → Option (List (Label × AVal D))
  | [], [] => some []
  | (l₁, a₁) :: fs₁, (l₂, a₂) :: fs₂ =>
      if l₁ = l₂ then (AVal.joinFields fs₁ fs₂).map ((l₁, a₁.join a₂) :: ·) else none
  | _, _ => none

end
noncomputable def AVal.joinAll : List (AVal D) → AVal D
  | [] => .fmt D.bot
  | [a] => a
  | a :: as => a.join (AVal.joinAll as)
def AVal.toFmt : AVal D → D.Fmt
  | .fmt F => F
  | _ => D.top
variable (D) in
/-- A format environment `Γ`. -/
abbrev AEnv := Var → Option (AVal D)
def AEnv.Holds (Γ : AEnv D) (σ : Store) : Prop :=
  ∀ x a, Γ x = some a → ∃ v, σ x = some v ∧ Describes a v
def AEnv.Le (Γ Γ' : AEnv D) : Prop := ∀ σ, Γ.Holds σ → Γ'.Holds σ
def AEnv.single (y : Var) (a : AVal D) : AEnv D := fun x => if x = y then some a else none
def AEnv.update (Γ : AEnv D) (x : Var) (a : AVal D) : AEnv D := Function.update Γ x (some a)
noncomputable def AEnv.join (Γ₁ Γ₂ : AEnv D) : AEnv D := fun x =>
  match Γ₁ x, Γ₂ x with
  | some a₁, some a₂ => some (a₁.join a₂)
  | _, _ => none
def Admits (κ : Option Val) (C : Val) : Prop := ∀ C₀ ∈ κ, C₀ = C
def Val.isReal : Val → Bool
  | .real => true
  | _ => false
variable (L D) in
/-- The analysis-specific operations of format inference. -/
structure Analysis where
  /-- `op♯` for rounded operators: a format bounding the exact result. -/
  arith : L.ArithOp → List D.Fmt → D.Fmt
  /-- `op♯` for unrounded operators. -/
  exact : L.ExactOp → List (AVal D) → AVal D
  /-- `F_C`, the format of a context, when the analysis understands it. -/
  ctxFmt : Val → Option D.Fmt
  /-- The context a record's abstract value determines, if any. -/
  ctxOf : AVal D → Option Val
  /-- Condition refinement `⟦e⟧♯` (for `true`) and `⟦¬e⟧♯` (for `false`). -/
  refine : Option Val → Expr L → Bool → AEnv D → AEnv D
def Analysis.rnd (A : Analysis L D) (κ : Option Val) (F : D.Fmt) : D.Fmt :=
  match κ with
  | none => D.top
  | some C =>
    if C.isReal then F
    else match A.ctxFmt C with
      | some FC => if D.sub F FC then F else FC
      | none => D.top
variable (A : Analysis L D) (Φ : Program L)
mutual

/-- `Γ, κ ⊢♯ e : a`. -/
inductive AEval : AEnv D → Option Val → Expr L → AVal D → Prop
  | bool {Γ κ b} : AEval Γ κ (.bool b) .other
  | num {Γ κ n} : AEval Γ κ (.num n) (.fmt (D.ofNum n))
  | real {Γ κ} : AEval Γ κ .real (.known .real)
  | var {Γ κ x a} : Γ x = some a → AEval Γ κ (.var x) a
  | list {Γ κ es as} : AEvalList Γ κ es as → AEval Γ κ (.list es) (.list (AVal.joinAll as))
  | index {Γ κ e₁ e₂ a a₂} : AEval Γ κ e₁ (.list a) → AEval Γ κ e₂ a₂ →
      AEval Γ κ (.index e₁ e₂) a
  | record {Γ κ fs afs} : AEvalFields Γ κ fs afs → AEval Γ κ (.record fs) (.record afs)
  | proj {Γ κ e afs l a} : AEval Γ κ e (.record afs) → afs.lookup l = some a →
      AEval Γ κ (.proj e l) a
  | ctx {Γ κ e a} : AEval Γ κ e a → AEval Γ κ (.ctx e) ((A.ctxOf a).elim .other .known)
  | arith {Γ κ op es as} : AEvalList Γ κ es as →
      AEval Γ κ (.arith op es) (.fmt (A.rnd κ (A.arith op (as.map AVal.toFmt))))
  | exact {Γ κ op es as} : AEvalList Γ κ es as → AEval Γ κ (.exact op es) (A.exact op as)
  | call {Γ κ f e y s a Γ' a'} : Φ f = some (y, s) → AEval Γ κ e a →
      AExec (.single y a) κ s Γ' a' → AEval Γ κ (.call f e) a'

inductive AEvalList : AEnv D → Option Val → List (Expr L) → List (AVal D) → Prop
  | nil {Γ κ} : AEvalList Γ κ [] []
  | cons {Γ κ e es a as} : AEval Γ κ e a → AEvalList Γ κ es as →
      AEvalList Γ κ (e :: es) (a :: as)

inductive AEvalFields : AEnv D → Option Val → List (Label × Expr L) →
    List (Label × AVal D) → Prop
  | nil {Γ κ} : AEvalFields Γ κ [] []
  | cons {Γ κ l e fs a afs} : AEval Γ κ e a → AEvalFields Γ κ fs afs →
      AEvalFields Γ κ ((l, e) :: fs) ((l, a) :: afs)

/-- `Γ, κ ⊢♯ s : ⟨Γ', a⟩`: `s` ends normally in `Γ'`, or returns a value
`a` describes. -/
inductive AExec : AEnv D → Option Val → Stmt L → AEnv D → AVal D → Prop
  | assign {Γ κ x e a} : AEval Γ κ e a → AExec Γ κ (.assign x e) (Γ.update x a) (.fmt D.bot)
  | skip {Γ κ} : AExec Γ κ .skip Γ (.fmt D.bot)
  | ret {Γ κ e a} : AEval Γ κ e a → AExec Γ κ (.ret e) Γ a
  | assert {Γ κ e a} : AEval Γ κ e a → AExec Γ κ (.assert e) (A.refine κ e true Γ) (.fmt D.bot)
  | seq {Γ κ s₁ s₂ Γ₁ Γ₂ a₁ a₂} : AExec Γ κ s₁ Γ₁ a₁ → AExec Γ₁ κ s₂ Γ₂ a₂ →
      AExec Γ κ (.seq s₁ s₂) Γ₂ (a₁.join a₂)
  | ite {Γ κ e s₁ s₂ Γ₁ Γ₂ a₁ a₂} : AExec (A.refine κ e true Γ) κ s₁ Γ₁ a₁ →
      AExec (A.refine κ e false Γ) κ s₂ Γ₂ a₂ →
      AExec Γ κ (.ite e s₁ s₂) (Γ₁.join Γ₂) (a₁.join a₂)
  | whileDo {Γ κ e s Γᵢ Γ' a} : Γ.Le Γᵢ → AExec (A.refine κ e true Γᵢ) κ s Γ' a → Γ'.Le Γᵢ →
      AExec Γ κ (.whileDo e s) (A.refine κ e false Γᵢ) a
  /-- The body runs under the context `e` is known to give. -/
  | withCtx {Γ κ e C s Γ' a} : AEval Γ (some .real) e (.known C) → AExec Γ (some C) s Γ' a →
      AExec Γ κ (.withCtx e s) Γ' a
  /-- The body runs under the unknown context `?`. -/
  | withUnknown {Γ κ e a₀ s Γ' a} : AEval Γ (some .real) e a₀ → AExec Γ none s Γ' a →
      AExec Γ κ (.withCtx e s) Γ' a

end
structure Analysis.Sound : Prop where
  arith : ∀ {op ns Fs n}, List.Forall₂ (fun n F => n ∈ D.γ F) ns Fs →
    L.arith op ns = some n → n ∈ D.γ (A.arith op Fs)
  exact : ∀ {op as vs v}, List.Forall₂ Describes as vs → L.exact op vs = some v →
    Describes (A.exact op as) v
  ctxFmt : ∀ {C FC r}, A.ctxFmt C = some FC → C.rnd L = some r →
    (∀ n, r n ∈ D.γ FC) ∧ ∀ n ∈ D.γ FC, r n = n
  ctxOf : ∀ {a C fs}, A.ctxOf a = some C → Describes a (.record fs) → C = .ctx fs
  refine : ∀ {Γ κ e b σ C}, Γ.Holds σ → Admits κ C → Eval Φ σ C e (.bool b) →
    (A.refine κ e b Γ).Holds σ
def Outcome.Within (Γ' : AEnv D) (a : AVal D) : Outcome → Prop
  | .normal σ => Γ'.Holds σ
  | .ret v => Describes a v
end Fpy


