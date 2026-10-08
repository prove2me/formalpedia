-- Prove2me | Theorems.Thm_d9Revenue_succ_eq_nextRevenue
-- name    : d9Revenue_succ_eq_nextRevenue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:22:18.226985+00:00
-- url     : https://prove2.me/theorems/47197d6a-432c-40ff-819d-84c84e2ca382
-- title:
--   d9Revenue_succ_eq_nextRevenue
-- statement:
--   Automatically extracted helper theorem d9Revenue_succ_eq_nextRevenue from oversized parent candidate 496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9NextRevenue
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_succ_eq_nextRevenue
    (f p x : ℕ → ℝ) (j : ℕ) (s : ℝ) :
    revenue f p x (j + 2) s =
      d9NextRevenue (fun t => revenue f p x (j + 1) t)
        (p (j + 1)) (x (j + 2)) (f (j + 2)) s := by sorry
