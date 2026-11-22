-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.toWord_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:00.207343+00:00
-- url     : https://prove2.me/submissions/62f3b5d6-53aa-45e6-8077-ec7bea683084

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_red

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
namespace PathIn
theorem _root_.solution [DecidableEq X] {h : X → ℝ} {P : ℝ → Prop} {p : ℝ}
    {xs : List (X × Bool)} (hx : PathIn (letterHeight h) P p xs) :
    PathIn (letterHeight h) P p (FreeGroup.mk xs).toWord := by
  rw [FreeGroup.toWord_mk]
  exact hx.red FreeGroup.reduce.red
end PathIn
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
