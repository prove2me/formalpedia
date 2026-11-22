-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.abelian_pullback_finitely_presented_on_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:27.519298+00:00
-- url     : https://prove2.me/submissions/f5c7bc96-eedb-4367-a09d-77722cae79fa

import Definitions.Def_Kourovka_Cofinality_CofinalCover
import Definitions.Def_Kourovka_Presentations_FreeAbelianPresentation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Finsupp
import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelian_pullback_finitely_presented
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_finite_presentation_on_fin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {α : Type} [Fintype α]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution (R : List (FreeGroup α)) :
    ∃ (n : ℕ) (S : List (FreeGroup (Fin n))),
      Nonempty (PresentedGroup (CentralExtension.relSet S) ≃*
        pullback Abelianization.of (abelianQuotientMap R)) := by
  obtain ⟨δ, hδ, T, hT⟩ := abelian_pullback_finitely_presented R
  letI := hδ
  exact finite_presentation_on_fin T hT
end Kourovka.MetabelianEnumeration.CofinalCover
