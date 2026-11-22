-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelian_pullback_finitely_presented
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.abelian_pullback_finitely_presented
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:24.903776+00:00
-- url     : https://prove2.me/theorems/fdfbfb56-8557-4388-aa1b-da4e315c6264
-- title:
--   Cofinal Cover: abelian pullback finitely presented
-- statement:
--   In particular the pullback used in the manuscript is finitely presented;
--   this statement does not assume metabelianity to obtain finite presentation.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/PullbackPresentation.lean#L77-L83
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/PullbackPresentation.lean#L77-L83

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

theorem Kourovka.MetabelianEnumeration.CofinalCover.abelian_pullback_finitely_presented (R : List (FreeGroup α)) :
    ∃ (δ : Type) (finiteδ : Fintype δ), letI := finiteδ
      ∃ T : List (FreeGroup δ),
        Nonempty (PresentedGroup (CentralExtension.relSet T) ≃*
          pullback Abelianization.of (abelianQuotientMap R)) := by sorry
