-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_two_local_preimages
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:34:20.685985+00:00
-- url     : https://prove2.me/submissions/fdbdd798-47e9-43aa-b42d-5874d9f86df6

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_psi_image
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_shiftQuad_factorisation
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_sublevel_isPreconnected
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
/-- Evaluation of the translated quadratic factor, including at zero. -/
theorem bottleneck_eval_shiftQuad (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (z : ℂ) :
    p.eval (cc + z) = p.eval cc + z ^ 2 * (shiftQuad p cc).eval z := by
  have heval : p.eval (cc + z) - p.eval cc =
      z ^ 2 * (shiftQuad p cc).eval z := by
    simpa only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_pow, add_comm z cc] using
      congrArg (fun q : Polynomial ℂ => q.eval z)
        (bottleneck_shiftQuad_factorisation p cc hcrit)
  exact (sub_eq_iff_eq_add.mp heval).trans (add_comm _ _)
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
/-- Paper (2.6): the exact quadratic normal form of `p` at the critical point. -/
theorem bottleneck_psi_sq (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (aHat : ℂ) (haHat : aHat ≠ 0) (z : ℂ) :
    p.eval (cc + z) - p.eval cc = aHat * bottleneckPsi p cc aHat z ^ 2 := by
  have hsq : Complex.sqrt (bottleneckQuot p cc aHat z) ^ 2 = bottleneckQuot p cc aHat z :=
    bottleneck_sqrt_sq _
  rw [bottleneck_eval_shiftQuad p cc hcrit z]
  unfold bottleneckPsi
  rw [mul_pow, hsq]
  unfold bottleneckQuot
  field_simp
  ring
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
/-- The two branches: every small value `η` and its negative are attained by `ψ`
inside the `h`-disc, giving two distinct preimages of `p cc + â η²` under `p`. -/
theorem bottleneck_two_preimages (p : Polynomial ℂ) (cc aHat : ℂ) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (η : ℂ) (hη : ‖η‖ < 4 / 5 * h) :
    ∃ zp ∈ Metric.ball (0 : ℂ) h, ∃ zm ∈ Metric.ball (0 : ℂ) h,
      bottleneckPsi p cc aHat zp = η ∧ bottleneckPsi p cc aHat zm = -η := by
  have himg := bottleneck_psi_image p cc aHat h hh hdisk
  obtain ⟨zp, hzp, hvp⟩ := himg (by simpa [Metric.mem_ball, dist_zero_right] using hη)
  obtain ⟨zm, hzm, hvm⟩ :=
    himg (show -η ∈ Metric.ball (0 : ℂ) (4 / 5 * h) by
      simpa [Metric.mem_ball, dist_zero_right] using hη)
  exact ⟨zp, hzp, zm, hzm, hvp, hvm⟩
theorem bottleneckNear_isPreconnected (p : Polynomial ℂ) (cc aHat : ℂ) (h s : ℝ)
    (hh : 0 < h) (hs : 0 < s) (hsh : 5 / 4 * s < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4) :
    IsPreconnected (bottleneckNear p cc aHat h s) := by
  have hballsub : Metric.ball (0 : ℂ) h ⊆ bottleneckPsiDomain p cc aHat :=
    Metric.ball_subset_closedBall.trans
      (bottleneck_closedBall_subset_psiDomain p cc aHat h hdisk)
  have hdiff : DifferentiableOn ℂ (bottleneckPsi p cc aHat) (Metric.ball (0 : ℂ) h) :=
    (bottleneck_psi_differentiableOn p cc aHat).mono hballsub
  have hlow : ∀ z ∈ Metric.ball (0 : ℂ) h, 4 / 5 * ‖z‖ ≤ ‖bottleneckPsi p cc aHat z‖ := by
    intro z hz
    exact bottleneck_psi_norm_lower p cc aHat h hdisk z
      (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hz))
  have hsub : bottleneckNear p cc aHat h s ⊆ Metric.closedBall (0 : ℂ) (5 / 4 * s) := by
    intro z hz
    have h1 := hlow z hz.1
    have h2 := hz.2
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  unfold bottleneckNear
  refine bottleneck_sublevel_isPreconnected (bottleneckPsi p cc aHat)
    (Metric.ball (0 : ℂ) h) Metric.isOpen_ball hdiff 0 (Metric.mem_ball_self hh) s ?_ ?_ ?_ ?_
  · simpa [bottleneckPsi] using hs
  · intro z hz hz0
    have hl := hlow z hz
    rw [hz0, norm_zero] at hl
    exact norm_le_zero_iff.mp (by linarith [norm_nonneg z])
  · exact Metric.isBounded_closedBall.subset hsub
  · exact (closure_minimal hsub Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hsh)
theorem bottleneckNear_shift_subset (p : Polynomial ℂ) (cc aHat : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (haHat : aHat ≠ 0)
    (h s δ : ℝ) (hh : 0 < h) (hs : 0 < s) (hsh : 5 / 4 * s < h)
    (hsδ : ‖aHat‖ * s ^ 2 ≤ δ) (hδ : δ = 1 - ‖p.eval cc‖)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4) :
    (fun z => cc + z) '' bottleneckNear p cc aHat h s ⊆
      connectedComponentIn (Omega p) cc := by
  have hpre := bottleneckNear_isPreconnected p cc aHat h s hh hs hsh hdisk
  have himgpre : IsPreconnected ((fun z => cc + z) '' bottleneckNear p cc aHat h s) :=
    hpre.image _ (by fun_prop)
  have hmem : cc ∈ (fun z => cc + z) '' bottleneckNear p cc aHat h s :=
    ⟨0, ⟨Metric.mem_ball_self hh, by simpa [bottleneckPsi] using hs⟩, by simp⟩
  refine himgpre.subset_connectedComponentIn hmem ?_
  rintro _ ⟨z, hz, rfl⟩
  have hval : p.eval (cc + z) - p.eval cc = aHat * bottleneckPsi p cc aHat z ^ 2 :=
    bottleneck_psi_sq p cc hcrit aHat haHat z
  have hnorm : ‖p.eval (cc + z) - p.eval cc‖ = ‖aHat‖ * ‖bottleneckPsi p cc aHat z‖ ^ 2 := by
    rw [hval, norm_mul, norm_pow]
  have htri : ‖p.eval (cc + z)‖ ≤ ‖p.eval cc‖ + ‖p.eval (cc + z) - p.eval cc‖ := by
    simpa using norm_add_le (p.eval cc) (p.eval (cc + z) - p.eval cc)
  have hpos : 0 < ‖aHat‖ := norm_pos_iff.mpr haHat
  have hlt : ‖aHat‖ * ‖bottleneckPsi p cc aHat z‖ ^ 2 < δ := by
    have h1 := hz.2
    have hnn := norm_nonneg (bottleneckPsi p cc aHat z)
    have hsq : ‖bottleneckPsi p cc aHat z‖ ^ 2 < s ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr h1)
        (show (0 : ℝ) < s + ‖bottleneckPsi p cc aHat z‖ by linarith)]
    have := mul_lt_mul_of_pos_left hsq hpos
    linarith
  show ‖p.eval (cc + z)‖ < 1
  rw [hnorm] at htri
  linarith
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h s δ : ℝ) (hh : 0 < h) (hs : 0 < s)
    (hsh : 5 / 4 * s < h) (hsδ : ‖aHat‖ * s ^ 2 ≤ δ) (hδ : δ = 1 - ‖p.eval cc‖)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (η : ℂ) (hη : η ≠ 0) (hηs : ‖η‖ < s) :
    ∃ x₁ ∈ connectedComponentIn (Omega p) cc, ∃ x₂ ∈ connectedComponentIn (Omega p) cc,
      x₁ ≠ x₂ ∧ p.eval x₁ = p.eval cc + aHat * η ^ 2 ∧
        p.eval x₂ = p.eval cc + aHat * η ^ 2 ∧
        ‖x₁ - cc‖ ≤ 5 / 4 * ‖η‖ ∧ ‖x₂ - cc‖ ≤ 5 / 4 * ‖η‖ := by
  have hηh : ‖η‖ < 4 / 5 * h := by linarith
  obtain ⟨zp, hzp, zm, hzm, hvp, hvm⟩ :=
    bottleneck_two_preimages p cc aHat h hh hdisk η hηh
  have hzpnorm : ‖zp‖ ≤ h :=
    le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hzp)
  have hzmnorm : ‖zm‖ ≤ h :=
    le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hzm)
  have hlowp := bottleneck_psi_norm_lower p cc aHat h hdisk zp hzpnorm
  rw [hvp] at hlowp
  have hlowm := bottleneck_psi_norm_lower p cc aHat h hdisk zm hzmnorm
  rw [hvm, norm_neg] at hlowm
  have hnear : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) h → ‖bottleneckPsi p cc aHat w‖ < s →
      cc + w ∈ connectedComponentIn (Omega p) cc := by
    intro w hw hpsi
    exact bottleneckNear_shift_subset p cc aHat hcrit haHat h s δ hh hs hsh hsδ hδ hdisk
      ⟨w, ⟨hw, hpsi⟩, rfl⟩
  have hmem₁ := hnear zp hzp (by rw [hvp]; exact hηs)
  have hmem₂ := hnear zm hzm (by rw [hvm, norm_neg]; exact hηs)
  have hevp : p.eval (cc + zp) = p.eval cc + aHat * η ^ 2 := by
    have hx := bottleneck_psi_sq p cc hcrit aHat haHat zp
    rw [hvp] at hx
    exact sub_eq_iff_eq_add'.mp hx
  have hevm : p.eval (cc + zm) = p.eval cc + aHat * η ^ 2 := by
    have hx := bottleneck_psi_sq p cc hcrit aHat haHat zm
    rw [hvm] at hx
    have hx2 : p.eval (cc + zm) - p.eval cc = aHat * η ^ 2 := by rw [hx]; ring
    exact sub_eq_iff_eq_add'.mp hx2
  refine ⟨cc + zp, hmem₁, cc + zm, hmem₂, ?_, hevp, hevm, ?_, ?_⟩
  · intro hEq
    have hzz : zp = zm := add_left_cancel hEq
    rw [hzz, hvm] at hvp
    refine hη ?_
    have h2 : (2 : ℂ) * η = 0 := by linear_combination -hvp
    simpa using h2
  · rw [add_sub_cancel_left]; linarith
  · rw [add_sub_cancel_left]; linarith
