-- Prove2me | Theorems.Thm_d9NextRevenue_hasDerivWithinAt_threshold_left
-- name    : d9NextRevenue_hasDerivWithinAt_threshold_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:36.885978+00:00
-- url     : https://prove2.me/theorems/bd02b5da-03e3-4582-87e4-c25a4f473b8a
-- title:
--   d9NextRevenue_hasDerivWithinAt_threshold_left
-- statement:
--   Automatically extracted helper theorem d9NextRevenue_hasDerivWithinAt_threshold_left from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_hasDerivWithinAt_threshold_left
    (g : ℝ → ℝ) (p x fare s r : ℝ)
    (hG : HasDerivWithinAt g r (Set.Iic p) p)
    (hps : p ≤ s) (hsx : s < p + x) :
    HasDerivWithinAt (fun u => d9NextRevenue g u x fare s) (r - fare)
      (Set.Iic p) p := by sorry
