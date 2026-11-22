-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.redStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:09.235177+00:00
-- url     : https://prove2.me/submissions/b4e423ab-4a60-4cce-a2f3-b9f208b6c47a

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_pathIn_append_iff

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
namespace PathIn
theorem _root_.solution {h : X → ℝ} {P : ℝ → Prop} {p : ℝ}
    {xs ys : List (X × Bool)} (hx : PathIn (letterHeight h) P p xs)
    (hr : FreeGroup.Red.Step xs ys) : PathIn (letterHeight h) P p ys := by
  cases hr with
  | @not as bs x b =>
    rw [pathIn_append_iff] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have hh := hx.2.2.2
    cases b <;> simpa [letterHeight, add_assoc] using hh
end PathIn
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
