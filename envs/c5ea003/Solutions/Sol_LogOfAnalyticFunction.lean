-- Prove2me | solution 1 for LogOfAnalyticFunction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:55:32.89897+00:00
-- url     : https://prove2.me/submissions/eab4048f-7c1c-4d66-a3b3-ebe6c4486b97

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix

-- from Zeta23.FromPNTPlus.StrongPNTPrefix
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/StrongPNT.lean (sorry-free prefix, truncated before JBlaschke/ZeroInequality).
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: kept only a prefix of the file (through `ZerosBound`: the Blaschke-factor /
Borel–Carathéodory bound on zeros in a disk; the remainder of StrongPNT.lean is not ported),
removed the Architect blueprint tooling (import Architect, blueprint_comment blocks,
@[blueprint ...] attributes), dropped the intra-project import of MediumPNT together with the
local notations and the `open ArithmeticFunction` that only the unported remainder used (the two Mathlib
imports previously reached through MediumPNT are imported directly), and added
`import Zeta23.Prelude.InstancePriorities` (this project's instance-priority settings).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory










open Classical












open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

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
      convert! this.div (BanalyticOnNhdOfDR.differentiableOn.differentiableAt
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
