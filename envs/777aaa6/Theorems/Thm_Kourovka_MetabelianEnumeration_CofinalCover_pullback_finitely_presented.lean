-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_pullback_finitely_presented
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.pullback_finitely_presented
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:15.855192+00:00
-- url     : https://prove2.me/theorems/41e1e37d-b3c1-4486-b35e-5207daf91b06
-- title:
--   Cofinal Cover: pullback finitely presented
-- statement:
--   The central pullback of an ordinary finitely presented group along a
--   surjective finite-rank free abelian map has an actual finite presentation.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/PullbackPresentation.lean#L44-L73
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/PullbackPresentation.lean#L44-L73

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

theorem Kourovka.MetabelianEnumeration.CofinalCover.pullback_finitely_presented
    (R : List (FreeGroup α)) {γ Q : Type} [Fintype γ] [CommGroup Q]
    (p : PresentedGroup (CentralExtension.relSet R) →* Q)
    (q : Multiplicative (FreeAbelianGroup γ) →* Q) (hq : Function.Surjective q) :
    ∃ (δ : Type) (finiteδ : Fintype δ), letI := finiteδ
      ∃ T : List (FreeGroup δ),
        Nonempty (PresentedGroup (CentralExtension.relSet T) ≃* pullback p q) := by sorry
