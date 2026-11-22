-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.lift_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:02.511397+00:00
-- url     : https://prove2.me/submissions/62479ab8-caae-4779-ac8a-43de0878e11a

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex



set_option autoImplicit true
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]
namespace Kourovka.Schreier.Transversal
theorem _root_.solution (f : S.Edge → H) (p w : FreeGroup X) :
    S.lift f (p * w) w⁻¹ = (S.lift f p w)⁻¹ := by
  apply mul_left_cancel (a := S.lift f p w)
  calc
    _ = 1 := by simpa only [mul_inv_cancel, lift_one] using (S.lift_mul f p w w⁻¹).symm
    _ = _ := (mul_inv_cancel _).symm
end Kourovka.Schreier.Transversal
