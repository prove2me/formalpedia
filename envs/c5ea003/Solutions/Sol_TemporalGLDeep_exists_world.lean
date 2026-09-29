-- Prove2me | solution 1 for TemporalGLDeep.exists_world
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T19:05:39.148798+00:00
-- url     : https://prove2.me/submissions/d730c010-bf56-455f-8578-5b8f970b144b

-- Sol generated from Logic/PosetTheory/TemporalGLCompleteness.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGLCompleteness
import Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
import Definitions.Def_Logic_PosetTheory_TemporalGLFiniteModel
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax
import Theorems.Thm_TemporalGLDeep_Der_mono
import Theorems.Thm_TemporalGLDeep_extend_list
import Theorems.Thm_TemporalGLDeep_not_mem_of_neg_mem

/-!
# Temporal Gödel–Löb logic: the finite canonical model and completeness

This file closes the last gap in the finite-model conjecture for the calculus TGL.
Rather than building an (infinite) canonical model — which for Gödel–Löb logic is *not*
a legal frame, since converse well-foundedness fails — we build the **finite canonical
model over the subformula closure of a single formula**, using exactly the relations
`filtR` / `filtT` from `TemporalGLFiniteModel.lean`.

Worlds are the consistent "decided subsets" `t ⊆ Cl` of a subformula-closed finite set
`Cl`: the list `gammaList Cl t` asserts every member of `t` and the negation of every
member of `Cl \ t`, and `t` is a world when that list is TGL-consistent.

The two existence lemmas are the mathematical core:

* `exists_box_succ` — if `◻B ∉ t`, there is a world `s` with `filtR Cl t s` and `B ∉ s`.
  Its proof runs the classical **Löb argument**: were the candidate hypothesis list
  inconsistent, boxing it and applying Löb's axiom would force `◻B ∈ t`.
* `exists_glob_succ` — the temporal analogue, whose proof uses `◼`-necessitation, the
  `4` axiom for `◼`, and the interaction axiom `◻A ⟹ ◼◻A`.

Combining these with the truth lemma `can_truth_lemma` yields

* `completeness` — every valid formula is derivable, and
* `finite_model_property` — **the conjecture**: every non-derivable `A` has a
  `TemporalGL.TempFrame` countermodel with at most `2 ^ (2 * subformulaCount A)` worlds.
-/

open TemporalGLDeep

open TemporalGL

/-! ## 1. Subformula-closed sets -/





/-! ## 2. Decided subsets and consistency -/









/-! ## 3. Lists of boxed / temporally boxed members of a world -/







/-! ## 4. The two existence lemmas -/



/-! ## 5. The finite canonical model -/


noncomputable instance (Cl : Finset TForm) : Fintype (CanWorld Cl) := FinsetCoe.fintype _





/-! ## 6. Completeness and the finite model property -/





/-! ## 7. Consequences and non-degeneracy

The results above are only interesting if TGL really is a non-trivial logic in which the
two modalities interact but do not collapse.  This section records that. -/









/-! ## 8. Machine-checked data points for the bound

The bound `2 ^ (2 * subformulaCount A)` is far from tight on concrete formulas; the two
theorems below record explicitly verified minimal countermodels, which are what a
bounded model search would actually return. -/




open TemporalGLDeep in
theorem solution(Cl : Finset TForm) (Γ : List TForm) (hΓ : ListCons Γ) :
    ∃ t, t ∈ CanW Cl ∧ (∀ x ∈ Γ, x ∈ Cl → x ∈ t) ∧ (∀ B : TForm, B.neg ∈ Γ → B ∉ t) := by
  obtain ⟨Γ', hsub, hdec, hcons⟩ := extend_list Cl.toList Γ hΓ
  classical
  refine ⟨Cl.filter (fun B => B ∈ Γ'), ?_, ?_, ?_⟩
  · refine mem_CanW.2 ⟨Finset.filter_subset _ _, ?_⟩
    intro hbad
    refine hcons (Der_mono (fun x hx => ?_) hbad)
    obtain ⟨B, hB, hBx⟩ := List.mem_map.1 hx
    rw [Finset.mem_toList] at hB
    by_cases hmem : B ∈ Cl.filter (fun B => B ∈ Γ')
    · rw [if_pos hmem] at hBx
      subst hBx
      exact (Finset.mem_filter.1 hmem).2
    · rw [if_neg hmem] at hBx
      subst hBx
      have hBΓ : B ∉ Γ' := fun hc => hmem (Finset.mem_filter.2 ⟨hB, hc⟩)
      rcases hdec B (Finset.mem_toList.2 hB) with h | h
      · exact absurd h hBΓ
      · exact h
  · intro x hx hxCl
    exact Finset.mem_filter.2 ⟨hxCl, hsub x hx⟩
  · intro B hB hmem
    have h1 : B ∈ Γ' := (Finset.mem_filter.1 hmem).2
    exact not_mem_of_neg_mem hcons h1 (hsub _ hB)
