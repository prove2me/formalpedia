-- Prove2me | Theorems.Thm_ConcaveOn_le_add_deriv_mul_sub
-- name    : ConcaveOn.le_add_deriv_mul_sub
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-11-04T03:01:08.4292+00:00
-- url     : https://prove2.me/theorems/c08e57be-79f7-45cc-89b3-e719c64578c9
-- title:
--   Concave functions lie below tangents
-- statement:
--   A differentiable concave real function lies below its tangent line, by trichotomy with slope bounds on each side.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/Convex/Deriv.lean#L10-L29

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
open Filter Set
open scoped Topology

namespace ConcaveOn

theorem le_add_deriv_mul_sub {s : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ s g) {x : ℝ} (hx : x ∈ s)
    (hdiff : DifferentiableAt ℝ g x) {y : ℝ} (hy : y ∈ s) :
    g y ≤ g x + deriv g x * (y - x) := by sorry

end ConcaveOn
