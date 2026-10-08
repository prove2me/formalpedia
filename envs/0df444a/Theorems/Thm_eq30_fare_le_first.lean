-- Prove2me | Theorems.Thm_eq30_fare_le_first
-- name    : eq30_fare_le_first
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T01:08:40.458031+00:00
-- url     : https://prove2.me/theorems/f15e8e84-f064-4a04-90f2-30312c568a9e
-- title:
--   eq30_fare_le_first
-- statement:
--   Automatically extracted helper theorem eq30_fare_le_first from oversized parent candidate aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30_fare_le_first
    (f : ℕ → ℝ) (hanti : ∀ k, 1 ≤ k → f (k + 1) < f k) :
    ∀ i, 1 ≤ i → f i ≤ f 1 := by sorry
