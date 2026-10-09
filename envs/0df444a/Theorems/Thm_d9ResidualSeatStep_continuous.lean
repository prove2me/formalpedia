-- Prove2me | Theorems.Thm_d9ResidualSeatStep_continuous
-- name    : d9ResidualSeatStep_continuous
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T14:40:29.269377+00:00
-- url     : https://prove2.me/theorems/437c8228-c60a-4157-9417-fd7b5136e2ef
-- title:
--   d9ResidualSeatStep_continuous
-- statement:
--   Automatically extracted helper theorem d9ResidualSeatStep_continuous from oversized parent candidate 639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Definitions.Def_d9ResidualSeatStep
import Theorems.Thm_d9ResidualSeatStep_eq_clipped
open NestedSeatAlloc.IntPolicy

theorem d9ResidualSeatStep_continuous
    (p x : ℕ → ℝ) (i : ℕ)
    (hp : 0 ≤ p i) (hx : 0 ≤ x (i + 1)) :
    Continuous (fun s => d9ResidualSeatStep p x i s) := by sorry
