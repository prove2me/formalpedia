-- Prove2me | Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
-- name    : Logic_PosetTheory_TemporalGLDeduction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:19.501931+00:00
-- url     : https://prove2.me/theorems/15919419-5be7-49ff-ac6f-28661ff09c14
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_TemporalGLDeduction
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.TemporalGLDeduction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/TemporalGLDeduction.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax

/-!
# Temporal Gödel–Löb logic: derivations from finite hypothesis lists

Working towards completeness of the calculus `TemporalGLDeep.Derivable`, this file sets
up the usual "sequent-like" interface on top of the Hilbert calculus:

`Der Γ X` means `⊢ x₁ ⟹ x₂ ⟹ ⋯ ⟹ xₙ ⟹ X` for `Γ = [x₁, …, xₙ]`.

Because the calculus takes *all* classical propositional tautologies as axioms, all the
propositional bookkeeping (weakening, cut, modus ponens, case analysis) reduces to the
single evaluation lemma `evalProp_implFold`, which is what `Der_taut_conseq` and
`Der_of_Der_taut` package.  The genuinely modal content is in

* `Der_box` : `Der Δ X → Der (Δ.map ◻) (◻X)` — necessitation plus iterated `K`,
* `Der_glob` : the temporal analogue,

both obtained from the distribution lemmas `boxDistrib` / `globDistrib`, proved by
induction on the hypothesis list.
-/

namespace TemporalGLDeep

/-! ## 1. Hypothesis lists -/

/-- `implFold [x₁,…,xₙ] X` is the formula `x₁ ⟹ ⋯ ⟹ xₙ ⟹ X`. -/
def implFold : List TForm → TForm → TForm
  | [], X => X
  | B :: Γ, X => B ⟹ implFold Γ X

/-- `Der Γ X`: `X` is derivable in TGL from the hypotheses `Γ`. -/
def Der (Γ : List TForm) (X : TForm) : Prop := Derivable (implFold Γ X)

theorem evalProp_implFold (v : TForm → Prop) (Γ : List TForm) (X : TForm) :
    evalProp v (implFold Γ X) ↔ ((∀ x ∈ Γ, evalProp v x) → evalProp v X) := by
  induction Γ with
  | nil => simp [implFold]
  | cons B Γ ih =>
      constructor
      · intro h hall
        exact (ih.1 (h (hall B (by simp)))) (fun x hx => hall x (by simp [hx]))
      · intro h hB
        refine ih.2 (fun hall => h (fun x hx => ?_))
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hB
        · exact hall x hx

/-- Every tautological consequence of `Γ` is derivable from `Γ`. -/
theorem Der_taut_conseq {Γ : List TForm} {X : TForm}
    (h : ∀ v : TForm → Prop, (∀ x ∈ Γ, evalProp v x) → evalProp v X) : Der Γ X :=
  Derivable.taut (fun v => (evalProp_implFold v Γ X).2 (h v))


theorem Der_of_mem {Γ : List TForm} {X : TForm} (h : X ∈ Γ) : Der Γ X :=
  Der_taut_conseq (fun _ hv => hv X h)

theorem Der_of_derivable {Γ : List TForm} {X : TForm} (h : Derivable X) : Der Γ X := by
  refine Derivable.mp (Derivable.taut (fun v => ?_)) h
  show evalProp v X → evalProp v (implFold Γ X)
  intro hX
  exact (evalProp_implFold v Γ X).2 (fun _ => hX)


theorem Der_mp {Γ : List TForm} {X Y : TForm} (h₁ : Der Γ (X ⟹ Y)) (h₂ : Der Γ X) :
    Der Γ Y := by
  have ht : Taut ((implFold Γ (X ⟹ Y)) ⟹ ((implFold Γ X) ⟹ implFold Γ Y)) := by
    intro v
    show evalProp v (implFold Γ (X ⟹ Y)) → evalProp v (implFold Γ X) →
      evalProp v (implFold Γ Y)
    intro ha hb
    exact (evalProp_implFold v Γ Y).2 (fun hv =>
      ((evalProp_implFold v Γ (X ⟹ Y)).1 ha hv) ((evalProp_implFold v Γ X).1 hb hv))
  exact Derivable.mp (Derivable.mp (Derivable.taut ht) h₁) h₂



/-! ## 2. Modal distribution over hypothesis lists -/






/-! ## 3. Consistency bookkeeping -/

/-- A hypothesis list is consistent if it does not derive `⊥`. -/
def ListCons (Γ : List TForm) : Prop := ¬ Der Γ TForm.bot



end TemporalGLDeep


