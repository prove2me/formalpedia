-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.finite_presentation_on_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:58.263716+00:00
-- url     : https://prove2.me/submissions/b5724d8f-914e-40bd-bc84-8dec0911a0a8

import Definitions.Def_Kourovka_Cofinality_CofinalCover
import Definitions.Def_Kourovka_Presentations_FreeAbelianPresentation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Finsupp
import Definitions.Def_Kourovka_Presentations_PullbackPresentation

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {α : Type} [Fintype α]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution (T : List (FreeGroup α)) {E : Type} [Group E]
    (hT : Nonempty (PresentedGroup (CentralExtension.relSet T) ≃* E)) :
    ∃ (n : ℕ) (S : List (FreeGroup (Fin n))),
      Nonempty (PresentedGroup (CentralExtension.relSet S) ≃* E) := by
  classical
  let e := Fintype.equivFin α
  let S := T.map (FreeGroup.freeGroupCongr e)
  have he : FreeGroup.freeGroupCongr e '' CentralExtension.relSet T =
      CentralExtension.relSet S := by
    ext w
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact List.mem_map.mpr ⟨r, hr, rfl⟩
    · intro hw
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
      exact ⟨r, hr, rfl⟩
  have h : Nonempty (PresentedGroup (CentralExtension.relSet T) ≃*
      PresentedGroup (CentralExtension.relSet S)) := by
    rw [← he]
    exact ⟨PresentedGroup.equivPresentedGroup _ e⟩
  exact ⟨Fintype.card α, S, ⟨h.some.symm.trans hT.some⟩⟩
end Kourovka.MetabelianEnumeration.CofinalCover
