-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:50:22.796864+00:00
-- url     : https://prove2.me/submissions/dabcfdcb-d5d9-4b7e-8c51-4ffe42f51d85

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
namespace PathIn
theorem _root_.solution {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs : List X}
    (h : PathIn f P p xs) : P p := by
  cases xs with
  | nil => exact h
  | cons x xs => exact h.1
end PathIn
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
