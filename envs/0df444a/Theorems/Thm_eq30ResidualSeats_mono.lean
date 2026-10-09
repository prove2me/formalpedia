-- Prove2me | Theorems.Thm_eq30ResidualSeats_mono
-- name    : eq30ResidualSeats_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:01:20.125696+00:00
-- url     : https://prove2.me/theorems/c566cfa0-c0f6-4d82-961d-6e7d3b82794f
-- title:
--   eq30ResidualSeats_mono
-- statement:
--   Automatically extracted helper theorem eq30ResidualSeats_mono from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30ClippedSeats
import Theorems.Thm_eq30ClippedSeats_increment_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30ResidualSeats_mono
    (p x s t : ℝ) (hx : 0 ≤ x) (hst : s ≤ t) :
    0 ≤ (t - eq30ClippedSeats p x t) -
      (s - eq30ClippedSeats p x s) := by sorry
