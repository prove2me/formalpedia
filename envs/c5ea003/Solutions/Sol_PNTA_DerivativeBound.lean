-- Prove2me | solution 1 for PNTA.DerivativeBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-12T06:11:31.442377+00:00
-- url     : https://prove2.me/submissions/e4a7bec7-9bc6-4e15-a179-a70075d792c7

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Theorems.Thm_PNTA_borelCaratheodory_prime

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
open Classical
open PNTA

private lemma cauchy_formula_deriv {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]

theorem solution {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (pos_r : 0 < r) (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (z_in_r : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [cauchy_formula_deriv r_lt_r' r'_lt_R analytic_f.differentiableOn  z_in_r, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[PNTA.borelCaratheodory_prime Mpos (by grind) r'_lt_R analytic_f f_zero_at_zero  re_f_le_M
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        dist_zero_right] at hz' z_in_r
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr
