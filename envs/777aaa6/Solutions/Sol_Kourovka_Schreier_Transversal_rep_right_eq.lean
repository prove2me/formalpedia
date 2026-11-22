-- Prove2me | solution 1 for Kourovka.Schreier.Transversal.rep_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:42.136178+00:00
-- url     : https://prove2.me/submissions/3e5b952f-9490-40d1-b4b9-dff84f00c96b

import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic
import Definitions.Def_Kourovka_Schreier_Transversal
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_mul

set_option autoImplicit true
open Kourovka Kourovka.Schreier
variable {X : Type*}
open Kourovka.Schreier.Transversal
variable {L : Subgroup (FreeGroup X)} (S : Transversal L)
namespace Kourovka.Schreier.Transversal
theorem _root_.solution {u v : FreeGroup X} (h : S.rep u = S.rep v) (w : FreeGroup X) :
    S.rep (u * w) = S.rep (v * w) := by
  rw [← S.rep_mul u w, ← S.rep_mul v w, h]
end Kourovka.Schreier.Transversal
