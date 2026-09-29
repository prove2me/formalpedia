-- Prove2me | solution 1 for TemporalGLDeep.Der_mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T19:02:43.040983+00:00
-- url     : https://prove2.me/submissions/4f58835d-f728-4e7c-8f12-6672bf1ef44d

-- Sol generated from Logic/PosetTheory/TemporalGLDeduction.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax
import Theorems.Thm_TemporalGLDeep_Der_of_Der_taut

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
theorem solution{Γ₁ Γ₂ : List TForm} {X : TForm} (hs : ∀ x ∈ Γ₁, x ∈ Γ₂) (h : Der Γ₁ X) :
    Der Γ₂ X :=
  Der_of_Der_taut (fun _ h1 hv => h1 (fun x hx => hv x (hs x hx))) h
