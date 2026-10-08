-- Prove2me | Theorems.Thm_d9ClippedSeats_increment_bounds
-- name    : d9ClippedSeats_increment_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:18.746332+00:00
-- url     : https://prove2.me/theorems/b0d62816-bc75-419c-8373-1920b9dc86ff
-- title:
--   d9ClippedSeats_increment_bounds
-- statement:
--   Automatically extracted helper theorem d9ClippedSeats_increment_bounds from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
open NestedSeatAlloc.IntPolicy

theorem d9ClippedSeats_increment_bounds
    (p x s t : ℝ) (hx : 0 ≤ x) (hst : s ≤ t) :
    0 ≤ d9ClippedSeats p x t - d9ClippedSeats p x s ∧
      d9ClippedSeats p x t - d9ClippedSeats p x s ≤ t - s := by sorry
