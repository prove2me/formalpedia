-- Prove2me | Theorems.Thm_Real_sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin
-- name    : Real.sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T13:53:55.755987+00:00
-- url     : https://prove2.me/theorems/814800bb-c990-4f14-941e-53805eff5b56
-- title:
--   Angle lifts differing by a constant
-- statement:
--   Two continuous real lifts of the same circle-valued map on a preconnected space differ by a constant: the difference range lands in $2\pi\mathbb{Z}$, a totally disconnected set.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/SpecialFunctions/AngleLift.lean#L7-L11

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Topology.Separation.Lemmas
open Real

namespace Real

theorem sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {θ ψ : X → ℝ} (hθ : Continuous θ) (hψ : Continuous ψ) (hcos : ∀ x, Real.cos (θ x) = Real.cos (ψ x)) (hsin : ∀ x, Real.sin (θ x) = Real.sin (ψ x)) (x y : X) : θ x - ψ x = θ y - ψ y := by sorry

end Real
