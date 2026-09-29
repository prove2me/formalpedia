-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_critical_fibre_singleton
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T01:16:13.983337+00:00
-- url     : https://prove2.me/submissions/79368255-31bf-4d2f-8b30-8f02befe5be2

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_no_three_preimages
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_two_local_preimages
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
theorem bottleneck_sqrt_sq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  have := Complex.cpow_nat_inv_pow w (n := 2) (by norm_num)
  simpa [Complex.sqrt] using this
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (p : Polynomial ℂ) (cc : ℂ)
    (hcrit : (Polynomial.derivative p).IsRoot cc) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (aHat : ℂ) (haHat : aHat ≠ 0) (h s δ : ℝ) (hh : 0 < h) (hs : 0 < s)
    (hsh : 5 / 4 * s < h) (hsδ : ‖aHat‖ * s ^ 2 ≤ δ) (hδ : δ = 1 - ‖p.eval cc‖)
    (hδpos : 0 < δ)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (z : ℂ) (hz : z ∈ connectedComponentIn (Omega p) cc) (hpz : p.eval z = p.eval cc) :
    z = cc := by
  by_contra hne
  have hApos : 0 < ‖aHat‖ := norm_pos_iff.mpr haHat
  have hOopen : IsOpen (Omega p) := isOpen_lt p.continuous.norm continuous_const
  have hUopen : IsOpen (connectedComponentIn (Omega p) cc) := hOopen.connectedComponentIn
  have hreg : (Polynomial.derivative p).eval z ≠ 0 := fun hzero => hne (huniq z hz hzero)
  obtain ⟨c₀, hc₀, he₀⟩ : ∃ e : OpenPartialHomeomorph ℂ ℂ, z ∈ e.source ∧ p.eval = ⇑e := by
    have hd := (p.hasStrictDerivAt z).hasStrictFDerivAt_equiv hreg
    exact ⟨hd.toOpenPartialHomeomorph p.eval, hd.mem_toOpenPartialHomeomorph_source, rfl⟩
  have hρpos : 0 < ‖z - cc‖ / 3 := by
    have : 0 < ‖z - cc‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    linarith
  set ρ : ℝ := ‖z - cc‖ / 3 with hρdef
  set V : Set ℂ := c₀.source ∩ connectedComponentIn (Omega p) cc ∩ Metric.ball z ρ with hVdef
  have hVopen : IsOpen V := (c₀.open_source.inter hUopen).inter Metric.isOpen_ball
  have hzV : z ∈ V := ⟨⟨hc₀, hz⟩, Metric.mem_ball_self hρpos⟩
  have hWopen : IsOpen (c₀ '' V) :=
    c₀.isOpen_image_of_subset_source hVopen (fun x hx => hx.1.1)
  have hvW : p.eval cc ∈ c₀ '' V := ⟨z, hzV, (congrFun he₀ z).symm.trans hpz⟩
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hWopen _ hvW
  set ν : ℝ := min s (4 * ρ / 5) with hνdef
  have hνpos : 0 < ν := lt_min hs (by linarith)
  set t' : ℝ := min (min (ε / 2) (δ / 2)) (ν ^ 2 * ‖aHat‖ / 2) with ht'def
  have ht'pos : 0 < t' :=
    lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have ht'ε : t' ≤ ε / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have ht'δ : t' ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have ht'ν : t' ≤ ν ^ 2 * ‖aHat‖ / 2 := min_le_right _ _
  have hn : ‖p.eval cc‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖p.eval cc / (‖p.eval cc‖ : ℂ)‖ = 1 := by simp [hn]
  set u : ℂ := p.eval cc / (‖p.eval cc‖ : ℂ) with hudef
  set ξ' : ℂ := p.eval cc + (t' : ℂ) * u with hξ'def
  have hξ'slit : ξ' ∈ bottleneckSlit (p.eval cc) :=
    ⟨t', ht'pos.le, by rw [← hδ]; linarith, rfl⟩
  have hdistξ' : ‖ξ' - p.eval cc‖ = t' := by
    rw [hξ'def, add_sub_cancel_left, norm_mul, hunit, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht'pos]
  have hξ'v : ξ' ≠ p.eval cc := by
    intro hEq
    rw [hEq, sub_self, norm_zero] at hdistξ'
    exact ht'pos.ne hdistξ'
  -- the value `η` of the two branches
  set η : ℂ := Complex.sqrt (((t' : ℂ) * u) / aHat) with hηdef
  have hη2 : aHat * η ^ 2 = (t' : ℂ) * u := by
    rw [hηdef, bottleneck_sqrt_sq, mul_div_cancel₀ _ haHat]
  have hηnormsq : ‖η‖ ^ 2 = t' / ‖aHat‖ := by
    have : ‖η‖ ^ 2 = ‖η ^ 2‖ := (norm_pow η 2).symm
    rw [this, hηdef, bottleneck_sqrt_sq, norm_div, norm_mul, hunit, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht'pos]
  have hηlt : ‖η‖ < ν := by
    have hsq : ‖η‖ ^ 2 < ν ^ 2 := by
      rw [hηnormsq]
      rw [div_lt_iff₀ hApos]
      nlinarith
    nlinarith [norm_nonneg η, hνpos]
  have hηne : η ≠ 0 := by
    intro hzero
    rw [hzero] at hη2
    simp at hη2
    rcases hη2 with hcase | hcase
    · exact ht'pos.ne' hcase
    · rw [hcase, norm_zero] at hunit; norm_num at hunit
  obtain ⟨x₁, hx₁, x₂, hx₂, hne12, hp1, hp2, hb1, hb2⟩ :=
    bottleneck_two_local_preimages p cc hcrit aHat haHat h s δ hh hs hsh hsδ hδ hdisk
      η hηne (lt_of_lt_of_le hηlt (min_le_left _ _))
  rw [hη2, ← hξ'def] at hp1 hp2
  -- the third preimage, next to `z`
  have hξ'W : ξ' ∈ c₀ '' V := by
    refine hεsub ?_
    rw [Metric.mem_ball, dist_eq_norm, hdistξ']
    linarith
  obtain ⟨y, hyV, hy⟩ := hξ'W
  have hpy : p.eval y = ξ' := (congrFun he₀ y).trans hy
  have hxρ : ∀ x : ℂ, ‖x - cc‖ ≤ 5 / 4 * ‖η‖ → ‖x - cc‖ < ρ := by
    intro x hx
    have h1 : ‖η‖ < 4 * ρ / 5 := lt_of_lt_of_le hηlt (min_le_right _ _)
    linarith
  have hyfar : ρ < ‖y - cc‖ := by
    have hyz : ‖y - z‖ < ρ := by
      have hb := Metric.mem_ball.mp hyV.2
      rwa [dist_eq_norm] at hb
    have htri : ‖z - cc‖ ≤ ‖z - y‖ + ‖y - cc‖ := by
      simpa using norm_add_le (z - y) (y - cc)
    rw [norm_sub_rev z y] at htri
    have h3 : ‖z - cc‖ = 3 * ρ := by rw [hρdef]; ring
    rw [h3] at htri
    linarith
  have hy₁ : y ≠ x₁ := fun hEq => absurd (hEq ▸ hyfar) (not_lt.mpr (hxρ x₁ hb1).le)
  have hy₂ : y ≠ x₂ := fun hEq => absurd (hEq ▸ hyfar) (not_lt.mpr (hxρ x₂ hb2).le)
  exact bottleneck_no_three_preimages p cc hv hcover b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros huniq
    ξ' hξ'slit hξ'v x₁ x₂ y hx₁ hx₂ hyV.1.2 hp1 hp2 hpy hne12
    (fun hEq => hy₁ hEq.symm) (fun hEq => hy₂ hEq.symm)
