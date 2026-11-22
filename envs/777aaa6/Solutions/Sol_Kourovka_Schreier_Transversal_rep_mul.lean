-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.rep_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:40:48.117967+00:00
-- url     : https://prove2.me/submissions/c48b07be-7824-45e8-9024-ef762dc249aa

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal

set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)
namespace Kourovka.Schreier.Transversal
theorem _root_.solution (u v : FreeGroup X) : S.rep (S.rep u * v) = S.rep (u * v) := by
  apply S.constantOnCosets
  have h := L.inv_mem (S.sameCoset u)
  convert h using 1
  group
end Kourovka.Schreier.Transversal
