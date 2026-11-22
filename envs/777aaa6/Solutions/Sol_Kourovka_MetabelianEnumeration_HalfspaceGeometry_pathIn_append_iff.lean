-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceGeometry.pathIn_append_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:58:24.522587+00:00
-- url     : https://prove2.me/submissions/59824cb5-b24e-4050-be71-27eb68ae0df5

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
theorem _root_.solution {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs ys : List X} :
    PathIn f P p (xs ++ ys) ↔
      PathIn f P p xs ∧ PathIn f P (p + (xs.map f).sum) ys := by
  induction xs generalizing p with
  | nil =>
    simp only [List.nil_append, List.map_nil, List.sum_nil, add_zero, PathIn]
    constructor
    · intro h
      have hstart : P p := by
        cases ys with
        | nil => exact h
        | cons y ys => exact h.1
      exact ⟨hstart, h⟩
    · exact And.right
  | cons x xs ih =>
    simp only [List.cons_append, PathIn, List.map_cons, List.sum_cons, ih, and_assoc,
      add_assoc]
end Kourovka.MetabelianEnumeration.HalfspaceGeometry
