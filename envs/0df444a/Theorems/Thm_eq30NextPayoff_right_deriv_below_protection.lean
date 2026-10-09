-- Prove2me | Theorems.Thm_eq30NextPayoff_right_deriv_below_protection
-- name    : eq30NextPayoff_right_deriv_below_protection
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:40:10.765045+00:00
-- url     : https://prove2.me/theorems/4b0f9e58-ab0b-4e61-9cf6-3e0b635b6cc5
-- title:
--   eq30NextPayoff_right_deriv_below_protection
-- statement:
--   Automatically extracted helper theorem eq30NextPayoff_right_deriv_below_protection from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30NextPayoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
open scoped Topology

theorem eq30NextPayoff_right_deriv_below_protection
    (g : ℝ → ℝ) (p x fare s d : ℝ) (hs : s < p)
    (hg : HasDerivWithinAt g d (Set.Ici s) s) :
    HasDerivWithinAt (fun t => eq30NextPayoff g p x fare t)
      d (Set.Ici s) s := by sorry
