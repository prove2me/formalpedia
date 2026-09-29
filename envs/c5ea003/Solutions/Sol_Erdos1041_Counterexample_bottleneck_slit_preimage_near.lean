-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_slit_preimage_near
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T01:18:12.681946+00:00
-- url     : https://prove2.me/submissions/2bb02484-5e0d-4371-8fff-66e39c9200a6

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_no_three_preimages
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_two_local_preimages
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_critical_fibre_singleton
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
/-- The distance along the slit is strictly smaller than its remaining radius. -/
theorem bottleneckSlit_norm_sub_lt (v w : ℂ) (hv : v ≠ 0)
    (hw : w ∈ bottleneckSlit v) : ‖w - v‖ < 1 - ‖v‖ := by
  obtain ⟨t, ht, ht', rfl⟩ := hw
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v / (‖v‖ : ℂ)‖ = 1 := by
    simp [hn]
  calc
    ‖v + (t : ℂ) * (v / (‖v‖ : ℂ)) - v‖ = |t| := by
      simp [div_self hn]
    _ = t := abs_of_nonneg ht
    _ < 1 - ‖v‖ := ht'
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
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (z : ℂ) (hz : z ∈ connectedComponentIn (Omega p) cc)
    (hslit : p.eval z ∈ bottleneckSlit (p.eval cc)) :
    ‖z - cc‖ < 4 / 3 * Real.sqrt (δ / ‖aHat‖) := by
  have hApos : 0 < ‖aHat‖ := norm_pos_iff.mpr haHat
  have hdivpos : 0 < δ / ‖aHat‖ := div_pos hδpos hApos
  set s : ℝ := Real.sqrt (δ / ‖aHat‖) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr hdivpos
  have hs2 : s ^ 2 = δ / ‖aHat‖ := Real.sq_sqrt hdivpos.le
  have hAs2 : ‖aHat‖ * s ^ 2 = δ := by
    rw [hs2, mul_div_cancel₀ _ (ne_of_gt hApos)]
  have hshalf : s < h / 2 := by
    have hlt : s ^ 2 < (h / 2) ^ 2 := by
      rw [hs2, div_lt_iff₀ hApos]
      nlinarith
    nlinarith [hspos, (by linarith : (0 : ℝ) < h / 2)]
  have hsh : 5 / 4 * s < h := by linarith
  by_cases hξv : p.eval z = p.eval cc
  · have hzc : z = cc :=
      bottleneck_critical_fibre_singleton p cc hcrit hv hcover aHat haHat h s δ hh hspos
        hsh (le_of_eq hAs2) hδ hδpos hdisk b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros huniq z hz hξv
    rw [hzc, sub_self, norm_zero]
    positivity
  · have ht : ‖p.eval z - p.eval cc‖ < δ := by
      have hx := bottleneckSlit_norm_sub_lt (p.eval cc) (p.eval z) hv hslit
      rw [← hδ] at hx
      exact hx
    set η : ℂ := Complex.sqrt ((p.eval z - p.eval cc) / aHat) with hηdef
    have hη2 : aHat * η ^ 2 = p.eval z - p.eval cc := by
      rw [hηdef, bottleneck_sqrt_sq, mul_div_cancel₀ _ haHat]
    have hηnormsq : ‖η‖ ^ 2 = ‖p.eval z - p.eval cc‖ / ‖aHat‖ := by
      have hx : ‖η‖ ^ 2 = ‖η ^ 2‖ := (norm_pow η 2).symm
      rw [hx, hηdef, bottleneck_sqrt_sq, norm_div]
    have hηnorm2 : ‖aHat‖ * ‖η‖ ^ 2 = ‖p.eval z - p.eval cc‖ := by
      rw [hηnormsq, mul_div_cancel₀ _ (ne_of_gt hApos)]
    have hηs : ‖η‖ < s := by
      have hmul : ‖aHat‖ * ‖η‖ ^ 2 < ‖aHat‖ * s ^ 2 := by rw [hηnorm2, hAs2]; exact ht
      have hsq : ‖η‖ ^ 2 < s ^ 2 := by nlinarith
      nlinarith [norm_nonneg η, hspos]
    have hηne : η ≠ 0 := by
      intro hzero
      rw [hzero] at hη2
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hη2
      exact hξv (sub_eq_zero.mp hη2.symm)
    obtain ⟨x₁, hx₁, x₂, hx₂, hne12, hp1, hp2, hbb1, hbb2⟩ :=
      bottleneck_two_local_preimages p cc hcrit aHat haHat h s δ hh hspos hsh
        (le_of_eq hAs2) hδ hdisk η hηne hηs
    rw [hη2] at hp1 hp2
    have hp1' : p.eval x₁ = p.eval z := by rw [hp1]; ring
    have hp2' : p.eval x₂ = p.eval z := by rw [hp2]; ring
    have hcase : z = x₁ ∨ z = x₂ := by
      by_contra hcon
      push_neg at hcon
      exact bottleneck_no_three_preimages p cc hv hcover b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros
        huniq (p.eval z) hslit (fun hEq => hξv hEq) x₁ x₂ z hx₁ hx₂ hz hp1' hp2' rfl
        hne12 (fun hEq => hcon.1 hEq.symm) (fun hEq => hcon.2 hEq.symm)
    rcases hcase with hEq | hEq
    · rw [hEq]; linarith
    · rw [hEq]; linarith
