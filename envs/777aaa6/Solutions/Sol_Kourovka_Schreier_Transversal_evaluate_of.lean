-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.evaluate_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:43:56.306052+00:00
-- url     : https://prove2.me/submissions/74a712bf-8f4a-4e2e-97b9-fa2bfb480689

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex

set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)
namespace Kourovka.Schreier.Transversal
theorem _root_.solution (z : S.Edge) : (S.evaluate (FreeGroup.of z)).val = S.edgeValue z := by
  simp [evaluate]
end Kourovka.Schreier.Transversal
