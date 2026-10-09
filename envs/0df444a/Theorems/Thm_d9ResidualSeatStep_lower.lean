-- Prove2me | Theorems.Thm_d9ResidualSeatStep_lower
-- name    : d9ResidualSeatStep_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:40:20.350101+00:00
-- url     : https://prove2.me/theorems/3d24f540-efec-49f2-a98c-9ac38f950e3f
-- title:
--   d9ResidualSeatStep_lower
-- statement:
--   Automatically extracted helper theorem d9ResidualSeatStep_lower from oversized parent candidate 639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Definitions.Def_d9ResidualSeatStep
import Theorems.Thm_d9ResidualSeatStep_eq_clipped
open NestedSeatAlloc.IntPolicy

theorem d9ResidualSeatStep_lower
    (p x : ℕ → ℝ) (i : ℕ) (s : ℝ)
    (hp : 0 ≤ p i) (hx : 0 ≤ x (i + 1)) :
    s - x (i + 1) ≤ d9ResidualSeatStep p x i s := by sorry
