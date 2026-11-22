-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.rewrite_eq_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:43.227811+00:00
-- url     : https://prove2.me/submissions/60c5a578-ee8e-4332-b754-33a76b18b940

import Definitions.Def_Kourovka_Schreier_Transversal
import Definitions.Def_Kourovka_Schreier_PathLifting
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
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
theorem _root_.solution [DecidableEq X] (p w : FreeGroup X) :
    S.rewrite p w = S.rewriteWord p w.toWord := by
  rw [← rewrite_mk, FreeGroup.mk_toWord]
end Kourovka.Schreier.Transversal
