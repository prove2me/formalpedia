-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.rep_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:58:38.54342+00:00
-- url     : https://prove2.me/submissions/c2e29cfd-3b6a-47f2-abf3-bc040bcd2dc3

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep

set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)
namespace Kourovka.Schreier.Transversal
theorem _root_.solution {u : FreeGroup X} (h : u ∈ L) : S.rep u = 1 := by
  rw [← S.rep_one]
  exact S.constantOnCosets (by simpa using h)
end Kourovka.Schreier.Transversal
