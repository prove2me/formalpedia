-- Prove2me | solution 1 for IntegratedInformation.exists_minimum_information_cut
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:02:13.718614+00:00
-- url     : https://prove2.me/submissions/13a9bbd3-fddd-46a8-b706-9c81e5c67179

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






















open IntegratedInformation in
theorem solution(S : CausalStructure) :
    ∃ c : S.Cut, S.loss c = Phi S := by
  simpa [Phi] using Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image S.loss) (Finset.univ_nonempty.image S.loss))
