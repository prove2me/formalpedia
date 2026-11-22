-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.edge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:45.88597+00:00
-- url     : https://prove2.me/submissions/123b9bb6-f3a0-4ece-ae52-5474b50b6c5d

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex

set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)
namespace Kourovka.Schreier.Transversal
theorem _root_.solution {p q : FreeGroup X} (h : S.rep p = S.rep q) (x : X) :
    S.edge p x = S.edge q x := by
  apply Prod.ext
  · exact Subtype.ext h
  · rfl
end Kourovka.Schreier.Transversal
