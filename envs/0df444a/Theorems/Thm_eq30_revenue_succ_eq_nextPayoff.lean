-- Prove2me | Theorems.Thm_eq30_revenue_succ_eq_nextPayoff
-- name    : eq30_revenue_succ_eq_nextPayoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:40:03.128185+00:00
-- url     : https://prove2.me/theorems/20706073-b297-43f4-ba4f-82e1f63e8f7b
-- title:
--   eq30_revenue_succ_eq_nextPayoff
-- statement:
--   Automatically extracted helper theorem eq30_revenue_succ_eq_nextPayoff from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30NextPayoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30_revenue_succ_eq_nextPayoff
    (f p x : ℕ → ℝ) (j : ℕ) (s : ℝ) :
    revenue f p x (j + 2) s =
      eq30NextPayoff (fun t => revenue f p x (j + 1) t)
        (p (j + 1)) (x (j + 2)) (f (j + 2)) s := by sorry
