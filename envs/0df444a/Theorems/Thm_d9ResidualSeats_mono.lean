-- Prove2me | Theorems.Thm_d9ResidualSeats_mono
-- name    : d9ResidualSeats_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:40:28.434118+00:00
-- url     : https://prove2.me/theorems/8826d117-0604-4145-9266-e68ff93383c9
-- title:
--   d9ResidualSeats_mono
-- statement:
--   Automatically extracted helper theorem d9ResidualSeats_mono from oversized parent candidate 639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Theorems.Thm_d9ClippedSeats_increment_bounds
open NestedSeatAlloc.IntPolicy

theorem d9ResidualSeats_mono
    (p x s t : ℝ) (hx : 0 ≤ x) (hst : s ≤ t) :
    0 ≤ (t - d9ClippedSeats p x t) - (s - d9ClippedSeats p x s) := by sorry
