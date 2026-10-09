-- Prove2me | Theorems.Thm_eq30RightSlope_eq_zero_of_threshold
-- name    : eq30RightSlope_eq_zero_of_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:51:24.411882+00:00
-- url     : https://prove2.me/theorems/94c92821-3217-4a57-b11a-1f6471036b27
-- title:
--   eq30RightSlope_eq_zero_of_threshold
-- statement:
--   Automatically extracted helper theorem eq30RightSlope_eq_zero_of_threshold from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30RightSlope
import Definitions.Def_eq30SlopeThreshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30RightSlope_eq_zero_of_threshold
    (f p x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ k s, eq30SlopeThreshold p x k ≤ s → eq30RightSlope f p x k s = 0 := by sorry
