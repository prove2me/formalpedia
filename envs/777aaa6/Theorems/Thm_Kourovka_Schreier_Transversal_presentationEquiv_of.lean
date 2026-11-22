-- Prove2me | Theorems.Thm_Kourovka_Schreier_Transversal_presentationEquiv_of
-- name    : Kourovka.Schreier.Transversal.presentationEquiv_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:18:36.828786+00:00
-- url     : https://prove2.me/theorems/d9c35984-f845-44bf-a132-ecab92b6fbf0
-- title:
--   Transversal: presentation Equiv of
-- statement:
--   The Transversal construction uses the presentation Equiv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/KernelPresentation.lean#L184-L191
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/KernelPresentation.lean#L184-L191

import Definitions.Def_Kourovka_Schreier_PathLifting
import Definitions.Def_Kourovka_Schreier_KernelPresentation
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)

theorem Kourovka.Schreier.Transversal.presentationEquiv_of (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) (z : S.Edge) :
    S.presentationEquiv R hR (PresentedGroup.of z) =
      QuotientGroup.mk' (relatorSubgroup (L := L) R) ⟨S.edgeValue z, S.edgeValue_mem z⟩ := by sorry
