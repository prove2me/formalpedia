-- Prove2me | Definitions.Def_Logic_PosetTheory_TemporalGLSyntax
-- name    : Logic_PosetTheory_TemporalGLSyntax
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:01:20.337585+00:00
-- url     : https://prove2.me/theorems/8dd6ea19-ff39-4593-8118-6a261ff4cf22
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_TemporalGLSyntax
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.TemporalGLSyntax`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/TemporalGLSyntax.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGL

/-!
# Temporal Gödel–Löb logic: syntax, Hilbert calculus, and soundness

`Catalog/Logic/PosetTheory/TemporalGL.lean` develops *temporal Gödel–Löb logic* (TGL)
in a **shallow** form: modal operators are combinators on predicates `W → Prop` over a
`TemporalGL.TempFrame`.  A shallow presentation cannot express a *finite model
property*, because there is no object-level notion of a formula, of its subformulas, or
of derivability.

This file supplies the missing **deep** layer:

* `TForm` — the object language: propositional atoms, `⊥`, `⟹`, the Gödel–Löb box `◻`
  and the temporal "always in the future" operator `◼`.
* `subformulas` / `subformulaCount` — the Fischer–Ladner style closure of a formula and
  its cardinality, the parameter of the finite-model bound.
* `TempModel` / `Sat` — Kripke semantics interpreting `TForm` on the catalog's
  `TemporalGL.TempFrame`, so that `Sat` for `◻`/`◼` is literally
  `TemporalGL.Box`/`TemporalGL.Glob`.
* `Derivable` — a Hilbert calculus **TGL**: all classical propositional tautologies,
  modus ponens, `K` and Löb for `◻`, `K`, `T` and `4` for `◼`, the *interaction axiom*
  `◻A ⟹ ◼◻A` matching `TempFrame.compat`, and the two necessitation rules.
* `soundness` — every theorem of TGL is valid on every temporal GL frame.  The `◻`-Löb
  case is discharged by the catalog theorem `TemporalGL.loeb_box_sound` and the
  interaction axiom by `TemporalGL.provability_persists`, so the calculus is exactly
  calibrated to the catalog's frame class.
* `not_derivable_bot`, `not_derivable_atom` — the calculus is consistent and does not
  prove everything (so the finite-model question is non-vacuous).
* `derivable_four` — a genuinely syntactic derivation: the `4` axiom `◻A ⟹ ◻◻A` is a
  *theorem* of TGL, derived from Löb (no transitivity axiom is assumed).

The filtration and the explicit `2 ^ (2 * subformulaCount A)` bound live in
`TemporalGLFiniteModel.lean`.
-/

namespace TemporalGLDeep

open TemporalGL

/-! ## 1. Object language -/

/-- Formulas of temporal Gödel–Löb logic. -/
inductive TForm where
  /-- A propositional atom. -/
  | atom : ℕ → TForm
  /-- Falsity. -/
  | bot : TForm
  /-- Implication. -/
  | imp : TForm → TForm → TForm
  /-- The Gödel–Löb provability box, interpreted along `TempFrame.R`. -/
  | box : TForm → TForm
  /-- The temporal "always in the future" operator, interpreted along `TempFrame.T`. -/
  | glob : TForm → TForm
  deriving DecidableEq, Repr

@[inherit_doc] scoped infixr:25 " ⟹ " => TForm.imp
@[inherit_doc] scoped prefix:80 "◻" => TForm.box
@[inherit_doc] scoped prefix:80 "◼" => TForm.glob

/-- Negation, as an abbreviation. -/
def TForm.neg (A : TForm) : TForm := A ⟹ TForm.bot

/-- Is the formula a `◻`? -/
def TForm.isBox : TForm → Bool
  | .box _ => true
  | _ => false

/-- Is the formula a `◼`? -/
def TForm.isGlob : TForm → Bool
  | .glob _ => true
  | _ => false

/-! ## 2. Subformulas -/

/-- The (finite) set of subformulas of a formula, including the formula itself. -/
def subformulas : TForm → Finset TForm
  | .atom p => {.atom p}
  | .bot => {.bot}
  | .imp B C => insert (.imp B C) (subformulas B ∪ subformulas C)
  | .box B => insert (.box B) (subformulas B)
  | .glob B => insert (.glob B) (subformulas B)

/-- The number of distinct subformulas of `A`.  This is the parameter appearing in the
finite-model bound `2 ^ (2 * subformulaCount A)`. -/
def subformulaCount (A : TForm) : ℕ := (subformulas A).card

/-- The syntactic size (number of nodes) of a formula. -/
def TForm.size : TForm → ℕ
  | .atom _ => 1
  | .bot => 1
  | .imp B C => B.size + C.size + 1
  | .box B => B.size + 1
  | .glob B => B.size + 1

@[simp] theorem self_mem_subformulas (A : TForm) : A ∈ subformulas A := by
  cases A <;> simp [subformulas]

/-- `subformulas` is closed under taking subformulas. -/
theorem subformulas_subset {A B : TForm} (h : B ∈ subformulas A) :
    subformulas B ⊆ subformulas A := by
  induction A with
  | atom p => simp [subformulas] at h; subst h; exact Finset.Subset.refl _
  | bot => simp [subformulas] at h; subst h; exact Finset.Subset.refl _
  | imp C D ihC ihD =>
      simp only [subformulas, Finset.mem_insert, Finset.mem_union] at h
      rcases h with h | h | h
      · subst h; exact Finset.Subset.refl _
      · exact (ihC h).trans (by intro x hx; simp [subformulas, Finset.mem_union]; tauto)
      · exact (ihD h).trans (by intro x hx; simp [subformulas, Finset.mem_union]; tauto)
  | box C ih =>
      simp only [subformulas, Finset.mem_insert] at h
      rcases h with h | h
      · subst h; exact Finset.Subset.refl _
      · exact (ih h).trans (by intro x hx; simp [subformulas]; tauto)
  | glob C ih =>
      simp only [subformulas, Finset.mem_insert] at h
      rcases h with h | h
      · subst h; exact Finset.Subset.refl _
      · exact (ih h).trans (by intro x hx; simp [subformulas]; tauto)




theorem mem_subformulas_glob {A B : TForm} (h : (◼B) ∈ subformulas A) :
    B ∈ subformulas A :=
  subformulas_subset h (by simp [subformulas, self_mem_subformulas])



/-! ## 3. Kripke semantics on the catalog's temporal GL frames -/

/-- A **temporal GL model**: a `TemporalGL.TempFrame` together with a valuation of the
propositional atoms. -/
structure TempModel where
  /-- The underlying temporal Gödel–Löb frame from the catalog. -/
  F : TempFrame
  /-- The valuation of propositional atoms. -/
  V : ℕ → F.W → Prop

/-- Satisfaction of a formula at a world. -/
def Sat (F : TempFrame) (V : ℕ → F.W → Prop) : TForm → F.W → Prop
  | .atom p, w => V p w
  | .bot, _ => False
  | .imp B C, w => Sat F V B w → Sat F V C w
  | .box B, w => ∀ v, F.R w v → Sat F V B v
  | .glob B, w => ∀ v, F.T w v → Sat F V B v

/-- `M ⊨ A` at world `w`. -/
def TempModel.sat (M : TempModel) (w : M.F.W) (A : TForm) : Prop := Sat M.F M.V A w








/-- Validity on the whole class of temporal GL frames. -/
def Valid (A : TForm) : Prop := ∀ (M : TempModel) (w : M.F.W), M.sat w A

/-! ## 4. Propositional tautologies of the object language -/

/-- Boolean-style evaluation of a formula treating atoms *and* every `◻`/`◼` formula as
an unanalysed propositional letter. -/
def evalProp (v : TForm → Prop) : TForm → Prop
  | .atom p => v (.atom p)
  | .bot => False
  | .imp B C => evalProp v B → evalProp v C
  | .box B => v (.box B)
  | .glob B => v (.glob B)

/-- `A` is a **classical propositional tautology** of the object language: it is true
under every assignment to atoms and to boxed/temporal formulas. -/
def Taut (A : TForm) : Prop := ∀ v : TForm → Prop, evalProp v A



/-! ## 5. The Hilbert calculus TGL -/

/-- The Hilbert-style calculus **TGL** for temporal Gödel–Löb logic. -/
inductive Derivable : TForm → Prop
  /-- Every classical propositional tautology is an axiom. -/
  | taut {A : TForm} : Taut A → Derivable A
  /-- Modus ponens. -/
  | mp {A B : TForm} : Derivable (A ⟹ B) → Derivable A → Derivable B
  /-- Distribution axiom `K` for the provability box. -/
  | boxK {A B : TForm} : Derivable ((◻(A ⟹ B)) ⟹ ((◻A) ⟹ ◻B))
  /-- Löb's axiom. -/
  | loeb {A : TForm} : Derivable ((◻((◻A) ⟹ A)) ⟹ ◻A)
  /-- Distribution axiom `K` for the temporal box. -/
  | globK {A B : TForm} : Derivable ((◼(A ⟹ B)) ⟹ ((◼A) ⟹ ◼B))
  /-- Reflexivity of time. -/
  | globT {A : TForm} : Derivable ((◼A) ⟹ A)
  /-- Transitivity of time. -/
  | glob4 {A : TForm} : Derivable ((◼A) ⟹ ◼◼A)
  /-- The interaction axiom matching `TempFrame.compat`: provability persists in time. -/
  | compatAx {A : TForm} : Derivable ((◻A) ⟹ ◼◻A)
  /-- Necessitation for the provability box. -/
  | boxNec {A : TForm} : Derivable A → Derivable (◻A)
  /-- Necessitation for the temporal box. -/
  | globNec {A : TForm} : Derivable A → Derivable (◼A)

/-! ## 6. Soundness -/


/-! ## 7. Non-triviality: the calculus is consistent and incomplete-as-a-set -/

/-- A one-world temporal GL frame with the empty accessibility relation. -/
def pointFrame : TempFrame where
  W := Unit
  R := fun _ _ => False
  T := fun _ _ => True
  R_trans := by intro a b c h _; exact h.elim
  R_wf := by
    constructor
    intro a
    exact ⟨a, fun y h => h.elim⟩
  T_refl := fun _ => trivial
  T_trans := by intro a b c _ _; trivial
  compat := by intro w w' v _ h; exact h.elim

/-- The one-world model in which the atom `p` is false everywhere. -/
def falseModel : TempModel where
  F := pointFrame
  V := fun _ _ => False



/-! ## 8. A syntactic derivation: the `4` axiom follows from Löb

No transitivity axiom is postulated in `Derivable`.  It is a classical fact about GL
that `◻A ⟹ ◻◻A` is nevertheless derivable from Löb's axiom; we carry the derivation
out in full, using the standard auxiliary formula `A ∧ ◻A`. -/

/-- Conjunction, encoded with `⟹` and `⊥`. -/
def TForm.and (A B : TForm) : TForm := (A ⟹ (B ⟹ TForm.bot)) ⟹ TForm.bot






end TemporalGLDeep


