-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:50:18.538506+00:00
-- url     : https://prove2.me/submissions/9e3b587a-d504-4c91-9a55-4a21dccf2956

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
namespace PathIn
theorem _root_.solution {f : X → ℝ} {P Q : ℝ → Prop} {p : ℝ} {xs : List X}
    (h : PathIn f P p xs) (hpq : ∀ x, P x → Q x) : PathIn f Q p xs := by
  induction xs generalizing p with
  | nil => exact hpq p h
  | cons x xs ih => exact ⟨hpq p h.1, ih h.2⟩
end PathIn
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
