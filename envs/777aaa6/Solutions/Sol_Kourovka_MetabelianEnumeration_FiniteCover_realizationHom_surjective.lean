-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.realizationHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:30.666766+00:00
-- url     : https://prove2.me/submissions/ba82f47e-f09c-4029-9305-321c80707188

import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Definitions.Def_Kourovka_Covers_FiniteCover
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_realizationHom_generator

set_option autoImplicit true
attribute [-instance] instConditionallyCompleteLinearOrder
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A)
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) :
    Function.Surjective (realizationHom data radius t A h) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  rw [Subgroup.closure_le]
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact ⟨PresentedGroup.of (Fin.castAdd a i), by
      simp [realizationHom_generator, generatorAssignment]⟩
  · exact ⟨PresentedGroup.of (Fin.natAdd k i), by
      simp [realizationHom_generator, generatorAssignment]⟩
end Kourovka.MetabelianEnumeration.FiniteCover
