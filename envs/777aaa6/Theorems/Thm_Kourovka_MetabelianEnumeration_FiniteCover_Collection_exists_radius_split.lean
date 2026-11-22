-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_exists_radius_split
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.exists_radius_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:39.768084+00:00
-- url     : https://prove2.me/theorems/61e06b89-a322-4f74-a40e-d7001772de95
-- title:
--   Collection: exists radius split
-- statement:
--   A near-boundary ordered word can be split into a short initial part
--   and a tail strictly inside the ball. Either block order is supported.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L230-L245
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L230-L245

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.exists_radius_split {k : ℕ} (hk : 1 ≤ k) (reverse : Bool)
    (u v : Lattice k) (ρ : ℝ) (hρ : 2 * (k : ℝ) < ρ)
    (hu : ‖euclidean u‖ ≤ ρ / (2 * k))
    (hv : ρ ≤ ‖euclidean v‖) (hv' : ‖euclidean v‖ < ρ + 1 / (2 * k)) :
    ∃ j : Fin k,
      ‖euclidean (latticeAbs u + latticeAbs (prefixStep reverse v j))‖ < ρ ∧
      ‖euclidean (tailStep reverse v j)‖ < ρ := by sorry
