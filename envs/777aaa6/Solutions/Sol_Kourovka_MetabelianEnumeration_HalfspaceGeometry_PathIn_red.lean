-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.red
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:51.042203+00:00
-- url     : https://prove2.me/submissions/effc23d8-0831-425d-97a0-f371e5ceef72

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_redStep

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
namespace PathIn
theorem _root_.solution {h : X → ℝ} {P : ℝ → Prop} {p : ℝ}
    {xs ys : List (X × Bool)} (hx : PathIn (letterHeight h) P p xs)
    (hr : FreeGroup.Red xs ys) : PathIn (letterHeight h) P p ys := by
  induction hr with
  | refl => exact hx
  | tail _ hstep ih => exact ih.redStep hstep
end PathIn
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
