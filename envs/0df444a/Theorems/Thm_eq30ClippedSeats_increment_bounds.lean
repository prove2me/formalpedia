-- Prove2me | Theorems.Thm_eq30ClippedSeats_increment_bounds
-- name    : eq30ClippedSeats_increment_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:41:00.191215+00:00
-- url     : https://prove2.me/theorems/9e3a11e7-7088-4071-ab4b-cd460aaf09c2
-- title:
--   eq30ClippedSeats_increment_bounds
-- statement:
--   Automatically extracted helper theorem eq30ClippedSeats_increment_bounds from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30ClippedSeats
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30ClippedSeats_increment_bounds
    (p x s t : ℝ) (hx : 0 ≤ x) (hst : s ≤ t) :
    0 ≤ eq30ClippedSeats p x t - eq30ClippedSeats p x s ∧
      eq30ClippedSeats p x t - eq30ClippedSeats p x s ≤ t - s := by sorry
