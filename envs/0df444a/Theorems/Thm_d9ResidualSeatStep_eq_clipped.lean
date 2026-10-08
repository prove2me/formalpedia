-- Prove2me | Theorems.Thm_d9ResidualSeatStep_eq_clipped
-- name    : d9ResidualSeatStep_eq_clipped
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:23:14.077763+00:00
-- url     : https://prove2.me/theorems/4cb145f9-8d17-4d5c-892e-83fa99aefe95
-- title:
--   d9ResidualSeatStep_eq_clipped
-- statement:
--   Automatically extracted helper theorem d9ResidualSeatStep_eq_clipped from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Definitions.Def_d9ResidualSeatStep
open NestedSeatAlloc.IntPolicy

theorem d9ResidualSeatStep_eq_clipped
    (p x : ℕ → ℝ) (i : ℕ) (s : ℝ)
    (hp : 0 ≤ p i) (hx : 0 ≤ x (i + 1)) :
    d9ResidualSeatStep p x i s =
      s - d9ClippedSeats (p i) (x (i + 1)) s := by sorry
