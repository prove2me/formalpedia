-- Prove2me | solution 1 for IntegratedInformation.exclusion_winner_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:08:30.028602+00:00
-- url     : https://prove2.me/submissions/248f5b8b-bfd6-448f-90dc-1c18cfd750ae

-- Sol generated from Novelty/IntegratedInformation.lean
import Mathlib
import Definitions.Def_Novelty_IntegratedInformation

/-! # Consciousness as Integrated Information

This file develops a finite mathematical model of integrated information.  A
causal structure has finitely many admissible cuts and a nonnegative loss at
each cut.  Its integrated information `Φ` is the least such loss.  Parallel
composition adds losses, while exclusion selects a maximally integrated member
of a finite family.  Pointwise comparison of loss functions supplies a small
category-like refinement calculus.
-/

open Finset

open IntegratedInformation


attribute [instance] CausalStructure.finiteCut CausalStructure.cutNonempty

















/-- Every candidate's integrated information is bounded by the exclusion
value. -/
theorem phi_le_bigPhi {ι : Type} [Fintype ι] [Nonempty ι]
    (F : CandidateFamily ι) (i : ι) : Phi (F.system i) ≤ BigPhi F := by
  exact Finset.le_max'
    (Finset.univ.image (fun j : ι => Phi (F.system j)))
    (Phi (F.system i))
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- The exclusion value is the least upper bound of the finite landscape of
candidate integrated-information values. -/
theorem bigPhi_le {ι : Type} [Fintype ι] [Nonempty ι]
    (F : CandidateFamily ι) {a : ℝ}
    (h : ∀ i, Phi (F.system i) ≤ a) : BigPhi F ≤ a := by
  apply (Finset.max'_le_iff _ _).2
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  exact h i




open IntegratedInformation in
theorem solution{ι : Type} [Fintype ι] [Nonempty ι]
    (F : CandidateFamily ι) (winner : ι)
    (h : ∀ i, i ≠ winner → Phi (F.system i) < Phi (F.system winner)) :
    ∀ i, Phi (F.system i) = BigPhi F → i = winner := by
  intro i hi
  by_contra hne
  have hlt := h i hne
  have hw : BigPhi F ≤ Phi (F.system winner) :=
    bigPhi_le F fun j => by
      by_cases hj : j = winner
      · subst j
        exact le_rfl
      · exact (h j hj).le
  have heq : BigPhi F = Phi (F.system winner) :=
    le_antisymm hw (phi_le_bigPhi F winner)
  linarith
