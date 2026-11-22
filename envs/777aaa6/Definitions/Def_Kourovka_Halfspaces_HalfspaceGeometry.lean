-- Prove2me | Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
-- name    : Kourovka_Halfspaces_HalfspaceGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:47:07.296189+00:00
-- url     : https://prove2.me/theorems/a90ad1e7-eb8b-4466-847c-d5718fe83d11
-- title:
--   Halfspace Geometry
-- statement:
--   Definitions and structural lemmas for Halfspace Geometry, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}
def PathIn (f : X → ℝ) (P : ℝ → Prop) (p : ℝ) : List X → Prop
  | [] => P p
  | x :: xs => P p ∧ PathIn f P (p + f x) xs
def letterHeight {Y : Type*} (h : Y → ℝ) (z : Y × Bool) : ℝ :=
  if z.2 then h z.1 else -h z.1
def Within (f : X → ℝ) (l u p : ℝ) : List X → Prop
  | [] => l ≤ p ∧ p ≤ u
  | x :: xs => (l ≤ p ∧ p ≤ u) ∧ Within f l u (p + f x) xs
end Kourovka.MetabelianEnumeration.HalfspaceGeometry


