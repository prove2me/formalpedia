-- Prove2me | solution 1 for PNTA.LogOfAnalyticFunction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-12T05:44:27.284571+00:00
-- url     : https://prove2.me/submissions/6cd64dfe-55cf-473f-928d-0b4177ab4dfa

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

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
open Classical

theorem solution {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  obtain ⟨J_B, hJB⟩ : ∃ J_B : ℂ → ℂ, (∀ z ∈ Metric.ball 0 R, (HasDerivAt J_B (deriv B z / B z) z)) ∧ J_B 0 = 0 ∧ (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
    set f : ℂ → ℂ := fun z => deriv B z / B z;
    have hf : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (BanalyticOnNhdOfDR.deriv.mono Metric.ball_subset_closedBall).div
        (BanalyticOnNhdOfDR.mono Metric.ball_subset_closedBall)
        (fun z hz => Bnonzero z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z ↦ J z - J 0, fun z hz ↦ (hJ z hz).sub_const _, by simp, ?_⟩
    set H : ℂ → ℂ := fun z => Complex.exp (J z - J 0) / B z
    have hJB_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt (fun z ↦ J z - J 0) (f z) z :=
      fun z hz ↦ (hJ z hz).sub_const _
    have hH_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt H 0 z := by
      intro z hz
      have := (Complex.hasDerivAt_exp _).comp z (hJB_deriv z hz)
      convert this.div (BanalyticOnNhdOfDR.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (Bnonzero z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have hH_const : ∀ z ∈ Metric.ball 0 R, H z = H 0 := by
      intro z hz
      have h_diffOn : DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz ↦ (hH_deriv z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) h_diffOn ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (hH_deriv x hx).hasFDerivAt.fderiv
    have h_exp_re : ∀ z ∈ Metric.ball 0 R, Real.exp (J z - J 0).re = ‖B z‖ / ‖B 0‖ := by
      intro z hz
      have hc := hH_const z hz
      simp only [H, sub_self, Complex.exp_zero, one_div] at hc
      rw [div_eq_iff (Bnonzero z (Metric.ball_subset_closedBall hz)), mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div, div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz := Bnonzero z (Metric.ball_subset_closedBall hz)
    have hB0 := Bnonzero 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← h_exp_re z hz, Real.log_exp]
  have hmem : ∀ z, z ∈ Metric.ball (0 : ℂ) r → z ∈ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [Metric.mem_ball] at hz
    linarith
  refine ⟨J_B, ?_, hJB.2.1, ?_, hJB.2.2⟩
  · intro z hz
    exact DifferentiableOn.analyticAt (fun w hw ↦ (hJB.1 w hw).differentiableAt.differentiableWithinAt) (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · intro z hz
    exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv
