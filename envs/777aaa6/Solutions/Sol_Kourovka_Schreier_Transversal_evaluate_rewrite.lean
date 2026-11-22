-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.evaluate_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:33.550403+00:00
-- url     : https://prove2.me/submissions/8d7d1763-8579-4d9e-9fb9-36216526230d

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
import Theorems.Thm_Kourovka_Schreier_Transversal_lift_map
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
import Theorems.Thm_Kourovka_Schreier_Transversal_lift_edgeValue
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
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
    (S.evaluate (S.rewrite p w)).val = S.rep p * w * (S.rep (p * w))⁻¹ := by
  have h := S.lift_map (L.subtype.comp S.evaluate) FreeGroup.of p w
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, evaluate_of,
    rewrite, lift_edgeValue] using h
end Kourovka.Schreier.Transversal
