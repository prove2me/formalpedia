-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_reorder_within
-- name    : Kourovka.MetabelianEnumeration.HalfspaceGeometry.reorder_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:48.665933+00:00
-- url     : https://prove2.me/theorems/2518be76-fc36-4caa-b5b9-b810e19761fa
-- title:
--   Halfspace Geometry: reorder within
-- statement:
--   Any finite list of bounded steps can be reordered to stay in a sufficiently
--   thick interval containing its initial and final vertices.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L154-L176
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L154-L176

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.HalfspaceGeometry.reorder_within (f : X → ℝ) (D l u p : ℝ) (xs : List X)
    (hD : ∀ x ∈ xs, |f x| ≤ D) (hwidth : 2 * D ≤ u - l)
    (hp : l ≤ p ∧ p ≤ u)
    (hend : l ≤ p + (xs.map f).sum ∧ p + (xs.map f).sum ≤ u) :
    ∃ ys : List X, ys.Perm xs ∧ Within f l u p ys := by sorry
