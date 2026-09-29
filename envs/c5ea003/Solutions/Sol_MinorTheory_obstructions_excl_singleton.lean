-- Prove2me | solution 1 for MinorTheory.obstructions_excl_singleton
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T08:09:36.996056+00:00
-- url     : https://prove2.me/submissions/44fc2863-d0ef-442b-afa2-5266c73de8e4

import Mathlib
import Definitions.Def_Novelty_OrderFramework

set_option autoImplicit false

private def indiscretePreorder : Preorder Bool where
  le _ _ := True
  lt _ _ := False
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  lt_iff_le_not_ge _ _ := by simp

private def indiscreteWellFounded :
    @WellFoundedLT Bool indiscretePreorder.toLT where
  wf := ⟨fun a => Acc.intro a (fun _ h => False.elim h)⟩

/-- Negation of the literal target: the last PartialOrder does not constrain
    the independently bound preorder used by excl and obstructions. -/
theorem solution : ¬ (∀ {α : Type} [p₁ : Preorder α] [p₂ : Preorder α]
    [@WellFoundedLT α p₂.toLT] [PartialOrder α] (H : α),
    @MinorTheory.obstructions α p₂ (@MinorTheory.excl α p₂ ({H} : Set α)) = {H}) := by
  intro h
  have heq := @h Bool indiscretePreorder indiscretePreorder
    indiscreteWellFounded inferInstance false
  have ht : true ∈ @MinorTheory.obstructions Bool indiscretePreorder
      (@MinorTheory.excl Bool indiscretePreorder ({false} : Set Bool)) := by
    constructor
    · intro hmem
      exact hmem (Set.mem_singleton false) trivial
    · intro x hlt
      exact False.elim hlt
  have hbad : true ∈ ({false} : Set Bool) := heq ▸ ht
  have : (true : Bool) = false := Set.mem_singleton_iff.mp hbad
  cases this
