-- Prove2me | Theorems.Thm_d9_hasDerivWithinAt_integral_of_slope_dct_left
-- name    : d9_hasDerivWithinAt_integral_of_slope_dct_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:28:44.876709+00:00
-- url     : https://prove2.me/theorems/54d3fb56-f0f3-42de-abe8-4f6254f15a40
-- title:
--   Left derivative of an integral from dominated convergence
-- statement:
--   Dominated convergence transfers a pointwise left derivative through an expectation, using slope quotients on the punctured left filter.
-- source:
--   Cause-linked repair of failed E150 publication d604613c-b94a-402f-8af6-d162f6be542b; exact extracted declaration 117, preamble adds MeasureTheory so Measure and Integrable resolve.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory
open NestedSeatAlloc.IntPolicy

theorem d9_hasDerivWithinAt_integral_of_slope_dct_left
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ → Ω → ℝ) (G : ℝ → ℝ) (D : Ω → ℝ)
    (B s : ℝ) (hs : 0 < s)
    (hG : ∀ t, G t = ∫ ω, F t ω ∂P)
    (hFInt : ∀ t, 0 ≤ t → t ≤ s → Integrable (F t) P)
    (hSlopeInt : ∀ t, 0 ≤ t → t ≤ s →
      Integrable (fun ω => slope (fun u => F u ω) s t) P)
    (hSlopeBound : ∀ t, 0 ≤ t → t ≤ s → ∀ ω,
      ‖slope (fun u => F u ω) s t‖ ≤ B)
    (hDeriv : ∀ ω, HasDerivWithinAt (fun t => F t ω) (D ω)
      (Set.Iic s) s)
    (hB : Integrable (fun _ : Ω => B) P) :
    HasDerivWithinAt G (∫ ω, D ω ∂P) (Set.Iic s) s := by sorry
