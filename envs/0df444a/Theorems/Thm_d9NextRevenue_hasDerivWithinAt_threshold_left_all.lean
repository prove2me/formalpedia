-- Prove2me | Theorems.Thm_d9NextRevenue_hasDerivWithinAt_threshold_left_all
-- name    : d9NextRevenue_hasDerivWithinAt_threshold_left_all
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T14:40:15.2748+00:00
-- url     : https://prove2.me/theorems/7542bdcd-3f8c-4a79-859d-525148f1a00f
-- title:
--   d9NextRevenue_hasDerivWithinAt_threshold_left_all
-- statement:
--   Automatically extracted helper theorem d9NextRevenue_hasDerivWithinAt_threshold_left_all from oversized parent candidate 639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:639a9ddd266f53936178d3317e77837b9af301f510884d3a73751f7b41da8a07

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
import Theorems.Thm_d9NextRevenue_hasDerivWithinAt_threshold_left
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_hasDerivWithinAt_threshold_left_all
    (g : ℝ → ℝ) (p x fare s r : ℝ)
    (hG : HasDerivWithinAt g r (Set.Iic p) p) (hx : 0 ≤ x) :
    HasDerivWithinAt (fun u => d9NextRevenue g u x fare s)
      (if p ≤ s ∧ s < p + x then r - fare else 0)
      (Set.Iic p) p := by sorry
