-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_exists_safe_step
-- name    : Kourovka.MetabelianEnumeration.HalfspaceGeometry.exists_safe_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:52.143089+00:00
-- url     : https://prove2.me/theorems/5952b6c6-f7c1-4bdd-9054-74dbeaa9ebe0
-- title:
--   Halfspace Geometry: exists safe step
-- statement:
--   At least one remaining step stays in a strip whose width is at least twice
--   the maximum step size, provided that both the present and final vertices lie
--   inside the strip.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L108-L150
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L108-L150

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.HalfspaceGeometry.exists_safe_step (f : X → ℝ) (D l u p : ℝ) (xs : List X)
    (hne : xs ≠ []) (hD : ∀ x ∈ xs, |f x| ≤ D)
    (hwidth : 2 * D ≤ u - l) (hp : l ≤ p ∧ p ≤ u)
    (hend : l ≤ p + (xs.map f).sum ∧ p + (xs.map f).sum ≤ u) :
    ∃ x ∈ xs, l ≤ p + f x ∧ p + f x ≤ u := by sorry
