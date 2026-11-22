-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.lift_edgeValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:46.034983+00:00
-- url     : https://prove2.me/submissions/7261ce6e-3dfd-4af6-b066-631f671bc161

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_mul
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex


attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk

set_option autoImplicit true
open Kourovka Kourovka.Schreier Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]
namespace Kourovka.Schreier.Transversal
theorem _root_.solution (p w : FreeGroup X) :
    S.lift S.edgeValue p w = S.rep p * w * (S.rep (p * w))⁻¹ := by
  rcases w with ⟨xs⟩
  change S.walk S.edgeValue p xs = _
  induction xs generalizing p with
  | nil => simp [walk, ← FreeGroup.one_eq_mk]
  | cons z xs ih => cases z with
    | mk x b =>
      cases b <;>
        simp [walk, edgeValue, edge, S.rep_mul, ih, mk_cons_true, mk_cons_false, mul_assoc]
end Kourovka.Schreier.Transversal
