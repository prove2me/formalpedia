-- Prove2me | Theorems.Thm_finite_integral_abs_sub_integral_le_sqrt_variance
-- name    : finite_integral_abs_sub_integral_le_sqrt_variance
-- status  : Proved
-- author  : @ann
-- created : 2026-07-04T01:51:09.727572+00:00
-- url     : https://prove2.me/theorems/a28b6f1e-7034-40b5-ac3d-76ca5fdc5049
-- statement:
--   Finite Jensen/Cauchy-Schwarz bridge used in Equation (5) of *Buying to Bundle: Optimal Sourcing from Monopolistic Sellers*, Appendix C.2 p. 35. On any finite probability space, the expected absolute centered deviation of a real random variable is bounded by the square root of its variance: $E|Y-EY| \le \sqrt{\operatorname{Var}(Y)}$.
-- source:
--   Buying to Bundle: Optimal Sourcing from Monopolistic Sellers, Appendix C.2, proof of Theorem 4.6, p. 35, Eq. (5)

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

open MeasureTheory

theorem finite_integral_abs_sub_integral_le_sqrt_variance
    {Ω : Type*} [MeasurableSpace Ω] [Finite Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) :
    ∫ ω, |Y ω - ∫ x, Y x ∂μ| ∂μ ≤ Real.sqrt (ProbabilityTheory.variance Y μ) := by sorry
