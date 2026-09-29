-- Prove2me | solution 1 for TemporalGLDeep.Der_glob
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:59:35.751673+00:00
-- url     : https://prove2.me/submissions/7b278d74-de1d-4df4-9bb0-3cb5d9e971a3

-- Sol generated from Logic/PosetTheory/TemporalGLDeduction.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
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

open TemporalGLDeep

/-! ## 1. Hypothesis lists -/












/-! ## 2. Modal distribution over hypothesis lists -/

/-- Composition inside a two-premise implication. -/
theorem derivable_comp2 {P Q R S : TForm} (h₁ : Derivable (P ⟹ (Q ⟹ R)))
    (h₂ : Derivable (R ⟹ S)) : Derivable (P ⟹ (Q ⟹ S)) := by
  have ht : Derivable ((P ⟹ (Q ⟹ R)) ⟹ ((R ⟹ S) ⟹ (P ⟹ (Q ⟹ S)))) :=
    Derivable.taut (fun _ a b c d => b (a c d))
  exact Derivable.mp (Derivable.mp ht h₁) h₂


/-- Distribution of `◼` over an implication fold. -/
theorem globDistrib (Δ : List TForm) (X : TForm) :
    Derivable ((◼(implFold Δ X)) ⟹ implFold (Δ.map TForm.glob) (◼X)) := by
  induction Δ generalizing X with
  | nil => exact Derivable.taut (fun _ h => h)
  | cons B Δ ih =>
      show Derivable ((◼(B ⟹ implFold Δ X)) ⟹
        ((◼B) ⟹ implFold (Δ.map TForm.glob) (◼X)))
      have hk : Derivable ((◼(B ⟹ implFold Δ X)) ⟹ ((◼B) ⟹ ◼(implFold Δ X))) :=
        Derivable.globK
      exact derivable_comp2 hk (ih X)



/-! ## 3. Consistency bookkeeping -/





open TemporalGLDeep in
theorem solution{Δ : List TForm} {X : TForm} (h : Der Δ X) : Der (Δ.map TForm.glob) (◼X) :=
  Derivable.mp (globDistrib Δ X) (Derivable.globNec h)
