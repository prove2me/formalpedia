-- Prove2me | Theorems.Thm_eq30_hasDerivWithinAt_of_right_affine
-- name    : eq30_hasDerivWithinAt_of_right_affine
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T01:08:22.590221+00:00
-- url     : https://prove2.me/theorems/6017370b-5864-4060-85f8-d5f55cd5a5a5
-- title:
--   eq30_hasDerivWithinAt_of_right_affine
-- statement:
--   Automatically extracted helper theorem eq30_hasDerivWithinAt_of_right_affine from oversized parent candidate aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30_hasDerivWithinAt_of_right_affine
    (g : ℝ → ℝ) (s d δ : ℝ) (hδ : 0 < δ)
    (haff : ∀ t, t ∈ Set.Ici s → t < s + δ →
      g t = g s + d * (t - s)) :
    HasDerivWithinAt g d (Set.Ici s) s := by sorry
