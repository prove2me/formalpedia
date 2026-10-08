-- Prove2me | Theorems.Thm_d9NextRevenue_eq_clipped
-- name    : d9NextRevenue_eq_clipped
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:27.217293+00:00
-- url     : https://prove2.me/theorems/20425d41-9baa-49e9-a20e-c8a274032a4c
-- title:
--   d9NextRevenue_eq_clipped
-- statement:
--   Automatically extracted helper theorem d9NextRevenue_eq_clipped from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Definitions.Def_d9NextRevenue
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_eq_clipped
    (g : ℝ → ℝ) (p x fare s : ℝ) (hx : 0 ≤ x) :
    d9NextRevenue g p x fare s =
      fare * d9ClippedSeats p x s +
        g (s - d9ClippedSeats p x s) := by sorry
