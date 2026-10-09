-- Prove2me | Theorems.Thm_eq30NextPayoff_eq_clipped
-- name    : eq30NextPayoff_eq_clipped
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:39:58.201619+00:00
-- url     : https://prove2.me/theorems/983ff84c-b855-4a49-b683-b0554d5dd4fd
-- title:
--   eq30NextPayoff_eq_clipped
-- statement:
--   Automatically extracted helper theorem eq30NextPayoff_eq_clipped from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30NextPayoff
import Definitions.Def_eq30ClippedSeats
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30NextPayoff_eq_clipped
    (g : ℝ → ℝ) (p x fare s : ℝ) (hx : 0 ≤ x) :
    eq30NextPayoff g p x fare s =
      fare * eq30ClippedSeats p x s +
        g (s - eq30ClippedSeats p x s) := by sorry
