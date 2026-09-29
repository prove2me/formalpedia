-- Prove2me | solution 1 for TemporalGLDeep.can_truth_lemma
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T19:11:58.68953+00:00
-- url     : https://prove2.me/submissions/d9af0ddf-6512-4da3-969b-11c6609a16b4

-- Sol generated from Logic/PosetTheory/TemporalGLCompleteness.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGL
import Definitions.Def_Logic_PosetTheory_TemporalGLCompleteness
import Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
import Definitions.Def_Logic_PosetTheory_TemporalGLFiniteModel
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax
import Theorems.Thm_TemporalGLDeep_Der_of_Der_taut
import Theorems.Thm_TemporalGLDeep_exists_box_succ
import Theorems.Thm_TemporalGLDeep_exists_glob_succ

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
theorem solution{Cl : Finset TForm} (hCl : Closed Cl) :
    ∀ B, B ∈ Cl → ∀ t : (canModel Cl hCl).F.W, ((canModel Cl hCl).sat t B ↔ B ∈ t.1) := by
  intro B
  induction B with
  | atom p => intro _ _; exact Iff.rfl
  | bot =>
      intro hmem t
      refine ⟨fun h => h.elim, fun h => ?_⟩
      exact absurd (Der_of_mem (mem_gammaList_pos hmem h)) (mem_CanW.1 t.2).2
  | imp B C ihB ihC =>
      intro hmem t
      obtain ⟨hBCl, hCCl⟩ := hCl.imp hmem
      have hcons := (mem_CanW.1 t.2).2
      have hB := ihB hBCl t
      have hC := ihC hCCl t
      constructor
      · intro h
        have h' : B ∈ t.1 → C ∈ t.1 := fun hb => hC.1 (h (hB.2 hb))
        refine mem_of_Der hcons hmem ?_
        by_cases hbt : B ∈ t.1
        · exact Der_of_Der_taut (fun _ h1 hv _ => h1 hv)
            (Der_of_mem (mem_gammaList_pos hCCl (h' hbt)))
        · exact Der_of_Der_taut (fun _ h1 hv hb => (h1 hv hb).elim)
            (Der_of_mem (mem_gammaList_neg hBCl hbt))
      · intro h hb
        refine hC.2 (mem_of_Der hcons hCCl ?_)
        exact Der_mp (Der_of_mem (mem_gammaList_pos hmem h))
          (Der_of_mem (mem_gammaList_pos hBCl (hB.1 hb)))
  | box B ih =>
      intro hmem t
      have hBCl := hCl.box hmem
      have hcons := (mem_CanW.1 t.2).2
      constructor
      · intro hsat
        by_contra hn
        obtain ⟨s, hsW, hRts, hBs⟩ := exists_box_succ hCl hcons hmem hn
        exact hBs ((ih hBCl ⟨s, hsW⟩).1 (hsat ⟨s, hsW⟩ hRts))
      · intro hin s hRs
        exact (ih hBCl s).2 (hRs.1 B hmem hin).1
  | glob B ih =>
      intro hmem t
      have hBCl := hCl.glob hmem
      have hcons := (mem_CanW.1 t.2).2
      constructor
      · intro hsat
        by_contra hn
        obtain ⟨s, hsW, hTts, hBs⟩ := exists_glob_succ hCl hcons hmem hn
        exact hBs ((ih hBCl ⟨s, hsW⟩).1 (hsat ⟨s, hsW⟩ hTts))
      · intro hin s hTs
        exact (ih hBCl s).2 (hTs.1 B hmem hin).1
