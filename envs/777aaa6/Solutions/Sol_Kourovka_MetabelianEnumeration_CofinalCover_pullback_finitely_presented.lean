-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.pullback_finitely_presented
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:36.352812+00:00
-- url     : https://prove2.me/submissions/c9094ae4-d556-43ab-8adb-a41c9c1bfda3

import Definitions.Def_Kourovka_Cofinality_CofinalCover
import Definitions.Def_Kourovka_Presentations_FreeAbelianPresentation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Finsupp
import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_kernel_free_abelian
import Theorems.Thm_Kourovka_MetabelianEnumeration_CentralExtension_finite_presentation_of_central_extension
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_first_kernel_central
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_first_surjective


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {α : Type} [Fintype α]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution
    (R : List (FreeGroup α)) {γ Q : Type} [Fintype γ] [CommGroup Q]
    (p : PresentedGroup (CentralExtension.relSet R) →* Q)
    (q : Multiplicative (FreeAbelianGroup γ) →* Q) (hq : Function.Surjective q) :
    ∃ (δ : Type) (finiteδ : Fintype δ), letI := finiteδ
      ∃ T : List (FreeGroup δ),
        Nonempty (PresentedGroup (CentralExtension.relSet T) ≃* pullback p q) := by
  letI : IsMulCommutative (Multiplicative (FreeAbelianGroup γ)) := ⟨⟨mul_comm⟩⟩
  obtain ⟨β, hβ, ⟨eβ⟩⟩ := kernel_free_abelian q
  letI := hβ
  let e := ((CentralExtension.freeAbelianPresentationEquiv β).trans eβ).trans
    (firstKernelEquiv p q).symm
  let ι := (first p q).ker.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp e.injective
  have hexact : ι.range = (first p q).ker := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e y).property
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hcentral : ι.range ≤ Subgroup.center (pullback p q) := by
    rw [hexact]
    exact first_kernel_central p q
  obtain ⟨T, hT⟩ := CentralExtension.finite_presentation_of_central_extension
    R (CentralExtension.abelianRelations β) (first p q) ι
      (first_surjective p q hq) hι hexact hcentral
  exact ⟨α ⊕ β, inferInstance, T, hT⟩
end Kourovka.MetabelianEnumeration.CofinalCover
