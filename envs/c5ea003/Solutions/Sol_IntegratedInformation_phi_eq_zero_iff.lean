-- Prove2me | solution 1 for IntegratedInformation.phi_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:08:28.154485+00:00
-- url     : https://prove2.me/submissions/0484f14b-0f26-43e0-9fd9-b7326f8af8a8

-- Sol generated from Novelty/IntegratedInformation.lean
import Mathlib
import Definitions.Def_Novelty_IntegratedInformation
import Theorems.Thm_IntegratedInformation_exists_minimum_information_cut
import Theorems.Thm_IntegratedInformation_phi_le_loss
import Theorems.Thm_IntegratedInformation_phi_nonneg

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
    Phi S = 0 ↔ ∃ c : S.Cut, S.loss c = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_minimum_information_cut S
    exact ⟨c, hc.trans h⟩
  · rintro ⟨c, hc⟩
    exact le_antisymm ((phi_le_loss S c).trans_eq hc) (phi_nonneg S)
