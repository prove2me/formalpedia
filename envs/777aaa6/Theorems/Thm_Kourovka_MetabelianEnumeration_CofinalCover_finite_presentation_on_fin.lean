-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_finite_presentation_on_fin
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.finite_presentation_on_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:15.353588+00:00
-- url     : https://prove2.me/theorems/dadc8926-625c-4688-bbea-8f5513c8bf55
-- title:
--   Cofinal Cover: finite presentation on fin
-- statement:
--   Reindexing a finite alphabet yields the ordinary generator-count format.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/PullbackPresentation.lean#L86-L106
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/PullbackPresentation.lean#L86-L106

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

theorem Kourovka.MetabelianEnumeration.CofinalCover.finite_presentation_on_fin (T : List (FreeGroup α)) {E : Type} [Group E]
    (hT : Nonempty (PresentedGroup (CentralExtension.relSet T) ≃* E)) :
    ∃ (n : ℕ) (S : List (FreeGroup (Fin n))),
      Nonempty (PresentedGroup (CentralExtension.relSet S) ≃* E) := by sorry
