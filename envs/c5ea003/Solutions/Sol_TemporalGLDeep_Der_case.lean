-- Prove2me | solution 1 for TemporalGLDeep.Der_case
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:59:34.660552+00:00
-- url     : https://prove2.me/submissions/ab37b799-047b-4286-8f38-afe9cc46c2d8

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






/-! ## 3. Consistency bookkeeping -/





open TemporalGLDeep in
theorem solution{Γ : List TForm} {B X : TForm} (h₁ : Der (B :: Γ) X)
    (h₂ : Der (B.neg :: Γ) X) : Der Γ X := by
  have ht : Taut ((implFold (B :: Γ) X) ⟹ ((implFold (B.neg :: Γ) X) ⟹ implFold Γ X)) := by
    intro v
    show evalProp v (implFold (B :: Γ) X) → evalProp v (implFold (B.neg :: Γ) X) →
      evalProp v (implFold Γ X)
    intro ha hb
    refine (evalProp_implFold v Γ X).2 (fun hv => ?_)
    by_cases hB : evalProp v B
    · refine (evalProp_implFold v (B :: Γ) X).1 ha (fun x hx => ?_)
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hB
      · exact hv x hx
    · refine (evalProp_implFold v (B.neg :: Γ) X).1 hb (fun x hx => ?_)
      rcases List.mem_cons.1 hx with rfl | hx
      · exact fun hc => (hB hc).elim
      · exact hv x hx
  exact Derivable.mp (Derivable.mp (Derivable.taut ht) h₁) h₂
