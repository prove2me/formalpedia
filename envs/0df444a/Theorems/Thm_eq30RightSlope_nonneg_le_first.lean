-- Prove2me | Theorems.Thm_eq30RightSlope_nonneg_le_first
-- name    : eq30RightSlope_nonneg_le_first
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T15:48:47.768289+00:00
-- url     : https://prove2.me/theorems/94c61aa7-ad8d-4b18-95dc-2ec21f63fbd2
-- title:
--   eq30RightSlope_nonneg_le_first
-- statement:
--   Automatically extracted helper theorem eq30RightSlope_nonneg_le_first from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30RightSlope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30RightSlope_nonneg_le_first
    (f p x : ℕ → ℝ)
    (hf_nonneg : ∀ i, 1 ≤ i → 0 ≤ f i)
    (hf_le_first : ∀ i, 1 ≤ i → f i ≤ f 1) :
    ∀ k s, 0 ≤ eq30RightSlope f p x k s ∧
      eq30RightSlope f p x k s ≤ f 1 := by sorry
