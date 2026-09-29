-- Prove2me | solution 1 for MinorTheory.Novelty.obstructions_excl_singleton
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T10:27:38.163976+00:00
-- url     : https://prove2.me/submissions/af0a3f2b-deb8-4cf6-a91e-3ce28c162c80

import Mathlib
import Definitions.Def_Speculative_AutoResearch_SingleForbiddenMinorLattice

set_option autoImplicit false

private def indiscretePreorder : Preorder Bool where
  le _ _ := True
  lt _ _ := False
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  lt_iff_le_not_ge _ _ := by simp

/-- The literal target binds two orders without requiring compatibility. -/
theorem solution : ¬ (∀ {α : Type} [p : Preorder α] [q : PartialOrder α] (H : α),
    @MinorTheory.Novelty.obstructions α q
      (@MinorTheory.Novelty.excl α p ({H} : Set α)) = {H}) := by
  intro h
  have heq := @h Bool indiscretePreorder inferInstance true
  have hf : false ∈ @MinorTheory.Novelty.obstructions Bool inferInstance
      (@MinorTheory.Novelty.excl Bool indiscretePreorder ({true} : Set Bool)) := by
    constructor
    · intro hmem
      exact hmem (Set.mem_singleton true) trivial
    · intro x hlt
      exact False.elim ((show ¬ x < (false : Bool) by cases x <;> decide) hlt)
  have hbad : false ∈ ({true} : Set Bool) := heq ▸ hf
  have : (false : Bool) = true := Set.mem_singleton_iff.mp hbad
  cases this

#print axioms solution
