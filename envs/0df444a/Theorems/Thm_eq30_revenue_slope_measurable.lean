-- Prove2me | Theorems.Thm_eq30_revenue_slope_measurable
-- name    : eq30_revenue_slope_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:01:03.971856+00:00
-- url     : https://prove2.me/theorems/5d1f2803-056f-4308-a5fd-b997429a9956
-- title:
--   eq30_revenue_slope_measurable
-- statement:
--   Automatically extracted helper theorem eq30_revenue_slope_measurable from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_eq30_revenue_measurable_comp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30_revenue_slope_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f p : ℕ → ℝ) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (k : ℕ) (s t : ℝ) :
    Measurable (fun ω =>
      slope (fun y => revenue f p (fun i => X i ω) k y) s t) := by sorry
