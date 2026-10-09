-- Prove2me | Theorems.Thm_eq30RightSlope_measurable
-- name    : eq30RightSlope_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T15:48:59.289044+00:00
-- url     : https://prove2.me/theorems/7342c4a0-78fc-44fe-acc6-e043f40db5ba
-- title:
--   eq30RightSlope_measurable
-- statement:
--   Automatically extracted helper theorem eq30RightSlope_measurable from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30RightSlope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30RightSlope_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    ∀ k (s : Ω → ℝ), Measurable s →
      Measurable (fun ω => eq30RightSlope f p (fun i => X i ω) k (s ω)) := by sorry
