-- Prove2me | Theorems.Thm_d9_hasDerivWithinAt_integral_of_slope_dct
-- name    : d9_hasDerivWithinAt_integral_of_slope_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:55:45.505987+00:00
-- url     : https://prove2.me/theorems/d07280c6-2562-44c2-9d33-6fdf21d2efa3
-- title:
--   d9_hasDerivWithinAt_integral_of_slope_dct
-- statement:
--   Automatically extracted helper d9_hasDerivWithinAt_integral_of_slope_dct from the oversized source-faithful proof of theorem1_all_seat_optimum_implies_intermediate_subdiff.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem d9_hasDerivWithinAt_integral_of_slope_dct
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ → Ω → ℝ) (G : ℝ → ℝ) (D : Ω → ℝ)
    (B s : ℝ)
    (hG : ∀ t, G t = ∫ ω, F t ω ∂P)
    (hFInt : ∀ t, s ≤ t → Integrable (F t) P)
    (hSlopeInt : ∀ t, s ≤ t →
      Integrable (fun ω => slope (fun u => F u ω) s t) P)
    (hSlopeBound : ∀ t, s ≤ t → ∀ ω,
      ‖slope (fun u => F u ω) s t‖ ≤ B)
    (hDeriv : ∀ ω, HasDerivWithinAt (fun t => F t ω) (D ω)
      (Set.Ici s) s)
    (hB : Integrable (fun _ : Ω => B) P) :
    HasDerivWithinAt G (∫ ω, D ω ∂P) (Set.Ici s) s := by sorry
