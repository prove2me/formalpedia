-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_psi_image
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:31:21.956157+00:00
-- url     : https://prove2.me/submissions/63ea1e4b-e1ed-400f-965c-1b5aaa7a6882

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_ball_subset_image
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

noncomputable section
open Topology

namespace Erdos1041.Counterexample
theorem bottleneckQuot_continuous (p : Polynomial ℂ) (cc aHat : ℂ) :
    Continuous (bottleneckQuot p cc aHat) :=
  (Polynomial.continuous _).div_const aHat
theorem bottleneckPsiDomain_isOpen (p : Polynomial ℂ) (cc aHat : ℂ) :
    IsOpen (bottleneckPsiDomain p cc aHat) :=
  Complex.isOpen_slitPlane.preimage (bottleneckQuot_continuous p cc aHat)
theorem bottleneck_sqrt_sq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  have := Complex.cpow_nat_inv_pow w (n := 2) (by norm_num)
  simpa [Complex.sqrt] using this
/-- The disk criterion bounds the normalised quadratic factor between `3/4` and
`5/4` in modulus. -/
theorem bottleneck_quot_norm_bounds (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ h) :
    3 / 4 ≤ ‖bottleneckQuot p cc aHat z‖ ∧ ‖bottleneckQuot p cc aHat z‖ ≤ 5 / 4 := by
  have hd : ‖bottleneckQuot p cc aHat z - 1‖ ≤ 1 / 4 := hdisk z hz
  have h1 : ‖bottleneckQuot p cc aHat z‖ - 1 ≤ ‖bottleneckQuot p cc aHat z - 1‖ := by
    simpa using norm_sub_norm_le (bottleneckQuot p cc aHat z) (1 : ℂ)
  have h2 : 1 - ‖bottleneckQuot p cc aHat z‖ ≤ ‖bottleneckQuot p cc aHat z - 1‖ := by
    have hx := norm_sub_norm_le (1 : ℂ) (bottleneckQuot p cc aHat z)
    rw [norm_sub_rev] at hx
    simpa using hx
  exact ⟨by linarith, by linarith⟩
/-- The normalised quadratic factor stays in the slit plane, so it has a
holomorphic square root. -/
theorem bottleneck_quot_mem_slitPlane (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ h) :
    bottleneckQuot p cc aHat z ∈ Complex.slitPlane := by
  have hd : ‖bottleneckQuot p cc aHat z - 1‖ ≤ 1 / 4 := hdisk z hz
  have hre : |(bottleneckQuot p cc aHat z - 1).re| ≤ ‖bottleneckQuot p cc aHat z - 1‖ :=
    Complex.abs_re_le_norm _
  have hsub : (bottleneckQuot p cc aHat z - 1).re = (bottleneckQuot p cc aHat z).re - 1 := by
    simp
  rw [hsub] at hre
  have hbounds := abs_le.mp hre
  exact Or.inl (by linarith [hbounds.1])
theorem bottleneck_closedBall_subset_psiDomain (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4) :
    Metric.closedBall (0 : ℂ) h ⊆ bottleneckPsiDomain p cc aHat := by
  intro z hz
  exact bottleneck_quot_mem_slitPlane p cc aHat h hdisk z
    (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
theorem bottleneck_sqrt_norm_bounds (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ h) :
    4 / 5 ≤ ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ ∧
      ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ ≤ 9 / 8 := by
  obtain ⟨hlo, hhi⟩ := bottleneck_quot_norm_bounds p cc aHat h hdisk z hz
  have hsq : ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ ^ 2 =
      ‖bottleneckQuot p cc aHat z‖ := by
    rw [← norm_pow, bottleneck_sqrt_sq]
  have hnn : 0 ≤ ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ := norm_nonneg _
  constructor
  · nlinarith
  · nlinarith
theorem bottleneck_psi_norm_lower (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ h) : 4 / 5 * ‖z‖ ≤ ‖bottleneckPsi p cc aHat z‖ := by
  have hb := (bottleneck_sqrt_norm_bounds p cc aHat h hdisk z hz).1
  have hnorm : ‖bottleneckPsi p cc aHat z‖ =
      ‖z‖ * ‖Complex.sqrt (bottleneckQuot p cc aHat z)‖ := by
    unfold bottleneckPsi; rw [norm_mul]
  rw [hnorm]
  nlinarith [norm_nonneg z]
theorem bottleneck_psi_differentiableOn (p : Polynomial ℂ) (cc aHat : ℂ) :
    DifferentiableOn ℂ (bottleneckPsi p cc aHat) (bottleneckPsiDomain p cc aHat) := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hq : DifferentiableAt ℂ (bottleneckQuot p cc aHat) z :=
    (((Polynomial.differentiable _).div_const aHat)).differentiableAt
  have h2 : DifferentiableAt ℂ (fun w => Complex.sqrt (bottleneckQuot p cc aHat w)) z :=
    (Complex.differentiableAt_sqrt hz).comp z hq
  have hid : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
  exact hid.mul h2
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4) :
    Metric.ball (0 : ℂ) (4 / 5 * h) ⊆ bottleneckPsi p cc aHat '' Metric.ball 0 h := by
  have hsub := bottleneck_closedBall_subset_psiDomain p cc aHat h hdisk
  have hdiffOn := bottleneck_psi_differentiableOn p cc aHat
  have hcont : ContinuousOn (bottleneckPsi p cc aHat) (Metric.closedBall 0 h) :=
    hdiffOn.continuousOn.mono hsub
  have hzero : bottleneckPsi p cc aHat 0 = 0 := by simp [bottleneckPsi]
  have hAn : AnalyticOnNhd ℂ (bottleneckPsi p cc aHat) (Metric.ball (0 : ℂ) h) := by
    have hall := hdiffOn.analyticOnNhd (bottleneckPsiDomain_isOpen p cc aHat)
    exact fun x hx => hall x (hsub (Metric.ball_subset_closedBall hx))
  -- `ψ` is not constant on the disc: it vanishes only at the origin
  have hz₁norm : ‖((h / 2 : ℝ) : ℂ)‖ = h / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < h / 2 by linarith)]
  have hz₁ : ((h / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) h := by
    rw [Metric.mem_ball, dist_zero_right, hz₁norm]
    linarith
  have himg : IsOpen (bottleneckPsi p cc aHat '' Metric.ball 0 h) := by
    rcases hAn.is_constant_or_isOpen (convex_ball (0 : ℂ) h).isPreconnected with ⟨w, hw⟩ | hopen
    · exfalso
      have h0 : bottleneckPsi p cc aHat 0 = w := hw 0 (Metric.mem_ball_self hh)
      have h1 : bottleneckPsi p cc aHat ((h / 2 : ℝ) : ℂ) = w := hw _ hz₁
      have hlow := bottleneck_psi_norm_lower p cc aHat h hdisk ((h / 2 : ℝ) : ℂ)
        (by rw [hz₁norm]; linarith)
      rw [hz₁norm, h1, ← h0, hzero] at hlow
      simp at hlow
      linarith
    · exact hopen _ (subset_refl _) Metric.isOpen_ball
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) h,
      4 / 5 * h ≤ ‖bottleneckPsi p cc aHat z - bottleneckPsi p cc aHat 0‖ := by
    intro z hz
    have hzn : ‖z‖ = h := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    rw [hzero, sub_zero]
    have hlow := bottleneck_psi_norm_lower p cc aHat h hdisk z (le_of_eq hzn)
    rwa [hzn] at hlow
  have hmain := bottleneck_ball_subset_image (bottleneckPsi p cc aHat) 0 h (4 / 5 * h)
    hh hcont himg hsphere
  rwa [hzero] at hmain
