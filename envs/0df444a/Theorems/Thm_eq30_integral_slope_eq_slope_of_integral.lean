-- Prove2me | Theorems.Thm_eq30_integral_slope_eq_slope_of_integral
-- name    : eq30_integral_slope_eq_slope_of_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:39:45.087974+00:00
-- url     : https://prove2.me/theorems/4375a8d4-497c-471f-9c2d-0798cbecc408
-- title:
--   eq30_integral_slope_eq_slope_of_integral
-- statement:
--   Automatically extracted helper theorem eq30_integral_slope_eq_slope_of_integral from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
theorem eq30_integral_slope_eq_slope_of_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ → Ω → ℝ) (G : ℝ → ℝ) (s t : ℝ)
    (hG : ∀ u, G u = ∫ ω, F u ω ∂P)
    (hFs : Integrable (F s) P) (hFt : Integrable (F t) P) :
    (∫ ω, slope (fun u => F u ω) s t ∂P) = slope G s t := by sorry
end
