-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_reorder_halfspaces
-- name    : Kourovka.MetabelianEnumeration.HalfspaceGeometry.reorder_halfspaces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:48.981367+00:00
-- url     : https://prove2.me/theorems/9711cf82-fa64-4887-9b8c-026f72b356c5
-- title:
--   Halfspace Geometry: reorder halfspaces
-- statement:
--   The interval common to the two halfspaces can be respected simultaneously;
--   outside it the path stays in the halfspace containing its endpoint.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L180-L192
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L180-L192

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.HalfspaceGeometry.reorder_halfspaces (f : X → ℝ) (D μ : ℝ) (xs : List X)
    (hD : ∀ x ∈ xs, |f x| ≤ D) (hD0 : 0 ≤ D) (hμ : 2 * D ≤ μ) :
    ∃ ys : List X, ys.Perm xs ∧
      Within f (min 0 (xs.map f).sum) (max μ (xs.map f).sum) 0 ys := by sorry
