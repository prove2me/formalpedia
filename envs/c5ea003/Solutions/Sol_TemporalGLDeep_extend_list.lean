-- Prove2me | solution 1 for TemporalGLDeep.extend_list
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T19:02:49.282207+00:00
-- url     : https://prove2.me/submissions/7863e590-6b8b-42aa-912d-4ce0fd5ba105

-- Sol generated from Logic/PosetTheory/TemporalGLDeduction.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax
import Theorems.Thm_TemporalGLDeep_Der_case

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
theorem solution(L : List TForm) : ∀ (Γ : List TForm), ListCons Γ →
    ∃ Γ', (∀ x ∈ Γ, x ∈ Γ') ∧ (∀ B ∈ L, B ∈ Γ' ∨ B.neg ∈ Γ') ∧ ListCons Γ' := by
  induction L with
  | nil => intro Γ h; exact ⟨Γ, fun _ hx => hx, by simp, h⟩
  | cons B L ih =>
      intro Γ h
      by_cases hB : Der (B :: Γ) TForm.bot
      · have h2 : ListCons (B.neg :: Γ) := fun hc => h (Der_case hB hc)
        obtain ⟨Γ', h1, h2', h3⟩ := ih (B.neg :: Γ) h2
        refine ⟨Γ', fun x hx => h1 x (List.mem_cons_of_mem _ hx), ?_, h3⟩
        intro C hC
        rcases List.mem_cons.1 hC with rfl | hC
        · exact Or.inr (h1 _ (by simp))
        · exact h2' C hC
      · obtain ⟨Γ', h1, h2', h3⟩ := ih (B :: Γ) hB
        refine ⟨Γ', fun x hx => h1 x (List.mem_cons_of_mem _ hx), ?_, h3⟩
        intro C hC
        rcases List.mem_cons.1 hC with rfl | hC
        · exact Or.inl (h1 _ (by simp))
        · exact h2' C hC
