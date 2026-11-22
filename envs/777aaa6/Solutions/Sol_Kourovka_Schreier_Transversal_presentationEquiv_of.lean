-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.presentationEquiv_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:44.350173+00:00
-- url     : https://prove2.me/submissions/57c72c76-fdb3-4498-b457-ed25250d16bb

import Definitions.Def_Kourovka_Schreier_PathLifting
import Definitions.Def_Kourovka_Schreier_KernelPresentation
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of



set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
namespace Kourovka.Schreier.Transversal
theorem _root_.solution (R : Set (FreeGroup X))
    (hR : Subgroup.normalClosure R ≤ L) (z : S.Edge) :
    S.presentationEquiv R hR (PresentedGroup.of z) =
      QuotientGroup.mk' (relatorSubgroup (L := L) R) ⟨S.edgeValue z, S.edgeValue_mem z⟩ := by
  change S.forward R hR (PresentedGroup.mk (S.relators R) (FreeGroup.of z)) = _
  rw [forward_mk]
  congr 1
  exact Subtype.ext (S.evaluate_of z)
end Kourovka.Schreier.Transversal
