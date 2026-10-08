-- Prove2me | Theorems.Thm_eq30_hasDerivWithinAt_sub_const
-- name    : eq30_hasDerivWithinAt_sub_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T01:08:45.896852+00:00
-- url     : https://prove2.me/theorems/3c9f2ea0-cc2c-4383-8b7b-5cc740011c99
-- title:
--   eq30_hasDerivWithinAt_sub_const
-- statement:
--   Automatically extracted helper theorem eq30_hasDerivWithinAt_sub_const from oversized parent candidate aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30_hasDerivWithinAt_sub_const
    (g : ℝ → ℝ) (s x d : ℝ)
    (hg : HasDerivWithinAt g d (Set.Ici (s - x)) (s - x)) :
    HasDerivWithinAt (fun t => g (t - x)) d (Set.Ici s) s := by sorry
