-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.abelian_pullback_finitely_presented
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:34.088251+00:00
-- url     : https://prove2.me/submissions/3697aeff-50db-41de-a152-bfd89d5a8032

import Definitions.Def_Kourovka_Cofinality_CofinalCover
import Definitions.Def_Kourovka_Presentations_FreeAbelianPresentation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Finsupp
import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_pullback_finitely_presented
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelianQuotientMap_surjective


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {α : Type} [Fintype α]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution (R : List (FreeGroup α)) :
    ∃ (δ : Type) (finiteδ : Fintype δ), letI := finiteδ
      ∃ T : List (FreeGroup δ),
        Nonempty (PresentedGroup (CentralExtension.relSet T) ≃*
          pullback Abelianization.of (abelianQuotientMap R)) :=
  pullback_finitely_presented R Abelianization.of (abelianQuotientMap R)
    (abelianQuotientMap_surjective R)
end Kourovka.MetabelianEnumeration.CofinalCover
