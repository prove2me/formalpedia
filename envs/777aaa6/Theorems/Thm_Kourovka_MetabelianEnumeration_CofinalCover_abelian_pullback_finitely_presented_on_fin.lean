-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_abelian_pullback_finitely_presented_on_fin
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.abelian_pullback_finitely_presented_on_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:55.434076+00:00
-- url     : https://prove2.me/theorems/f5ace4ba-7609-4bd1-806c-e94d99d187c6
-- title:
--   Cofinal Cover: abelian pullback finitely presented on fin
-- statement:
--   The Cofinal Cover construction uses the abelian pullback finitely presented on fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/PullbackPresentation.lean#L108-L114
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/PullbackPresentation.lean#L108-L114

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

theorem Kourovka.MetabelianEnumeration.CofinalCover.abelian_pullback_finitely_presented_on_fin (R : List (FreeGroup α)) :
    ∃ (n : ℕ) (S : List (FreeGroup (Fin n))),
      Nonempty (PresentedGroup (CentralExtension.relSet S) ≃*
        pullback Abelianization.of (abelianQuotientMap R)) := by sorry
