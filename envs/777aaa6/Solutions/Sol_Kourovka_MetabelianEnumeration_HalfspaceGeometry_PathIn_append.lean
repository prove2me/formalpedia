-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:58:23.986287+00:00
-- url     : https://prove2.me/submissions/c30a4397-b354-4d8f-9d0d-22e077d26ff4

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
namespace PathIn
theorem _root_.solution {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs ys : List X}
    (hx : PathIn f P p xs) (hy : PathIn f P (p + (xs.map f).sum) ys) :
    PathIn f P p (xs ++ ys) := by
  induction xs generalizing p with
  | nil => simpa using hy
  | cons x xs ih =>
    exact ⟨hx.1, ih hx.2 (by simpa only [List.map_cons, List.sum_cons, add_assoc] using hy)⟩
end PathIn
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
