-- Prove2me | Theorems.Thm_d9ResidualSeats_nonneg
-- name    : d9ResidualSeats_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:11.556258+00:00
-- url     : https://prove2.me/theorems/4291dfd0-0d9c-44ce-a790-0944f425bd6b
-- title:
--   d9ResidualSeats_nonneg
-- statement:
--   Automatically extracted helper theorem d9ResidualSeats_nonneg from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
open NestedSeatAlloc.IntPolicy

theorem d9ResidualSeats_nonneg
    (p x s : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) :
    0 ≤ s - d9ClippedSeats p x s := by sorry
