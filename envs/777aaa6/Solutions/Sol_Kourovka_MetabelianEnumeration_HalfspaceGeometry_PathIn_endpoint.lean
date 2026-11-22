-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:35.707267+00:00
-- url     : https://prove2.me/submissions/0cf020fd-219a-4a33-907d-8f936bced618

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
namespace PathIn
theorem _root_.solution {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs : List X}
    (h : PathIn f P p xs) : P (p + (xs.map f).sum) := by
  induction xs generalizing p with
  | nil => simpa [PathIn] using h
  | cons x xs ih => simpa only [List.map_cons, List.sum_cons, add_assoc] using ih h.2
end PathIn
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
