-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.Within.pathIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:38.865209+00:00
-- url     : https://prove2.me/submissions/50de8c0a-30c3-4d56-b53e-e4b9bc9e6f8e

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
namespace Within
theorem _root_.solution {f : X → ℝ} {l u p : ℝ} {xs : List X}
    (h : Within f l u p xs) : PathIn f (fun x => l ≤ x ∧ x ≤ u) p xs := by
  induction xs generalizing p with
  | nil => exact h
  | cons x xs ih => exact ⟨h.1, ih h.2⟩
end Within
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
