-- Prove2me | solution 1 for TemporalGLDeep.Der_cut
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:59:35.196779+00:00
-- url     : https://prove2.me/submissions/c5ea197d-c5f4-4ff3-a17d-792fde649006

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
theorem solution{Γ Δ : List TForm} {X : TForm} (h : ∀ x ∈ Δ, Der Γ x) (hd : Der Δ X) :
    Der Γ X := by
  have main : ∀ (Δ : List TForm) (X : TForm), (∀ x ∈ Δ, Der Γ x) →
      Der Γ (implFold Δ X) → Der Γ X := by
    intro Δ
    induction Δ with
    | nil => intro X _ h; exact h
    | cons B Δ ih =>
        intro X hmem hfold
        refine ih X (fun x hx => hmem x (by simp [hx])) ?_
        exact Der_mp hfold (hmem B (by simp))
  exact main Δ X h (Der_of_derivable hd)
