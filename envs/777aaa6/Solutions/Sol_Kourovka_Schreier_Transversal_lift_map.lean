-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.lift_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:35.848782+00:00
-- url     : https://prove2.me/submissions/7c8e3ce6-13db-4904-8e8b-2f201e02efc4

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
theorem _root_.solution {K : Type*} [Group K] (φ : H →* K) (f : S.Edge → H)
    (p w : FreeGroup X) : φ (S.lift f p w) = S.lift (fun z => φ (f z)) p w := by
  rcases w with ⟨xs⟩
  change φ (S.walk f p xs) = S.walk (fun z => φ (f z)) p xs
  induction xs generalizing p with
  | nil => exact φ.map_one
  | cons z xs ih => cases z with
    | mk x b => cases b <;> simp only [walk, map_mul, map_inv, ih]
end Kourovka.Schreier.Transversal
