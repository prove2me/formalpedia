-- Prove2me | Theorems.Thm_d9NextRevenue_lipschitz_parameter
-- name    : d9NextRevenue_lipschitz_parameter
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:24.782836+00:00
-- url     : https://prove2.me/theorems/c17572b1-dd92-4107-b7da-4bde2cbd85b4
-- title:
--   d9NextRevenue_lipschitz_parameter
-- statement:
--   Automatically extracted helper theorem d9NextRevenue_lipschitz_parameter from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_lipschitz_parameter
    (G : ℝ → ℝ → ℝ) (u v p x fare s L : ℝ)
    (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hG : ∀ t, 0 ≤ t → |G u t - G v t| ≤ L * |u - v|) :
    |d9NextRevenue (G u) p x fare s -
      d9NextRevenue (G v) p x fare s| ≤ L * |u - v| := by sorry
