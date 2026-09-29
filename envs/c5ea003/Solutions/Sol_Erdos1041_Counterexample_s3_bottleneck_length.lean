-- Prove2me | solution 1 for Erdos1041.Counterexample.s3_bottleneck_length
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T01:21:28.79104+00:00
-- url     : https://prove2.me/submissions/920870e8-aec0-4ae6-ada2-845ea9dd49ed

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_length_via_point
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_natDegree_pos
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_path_meets_slit_of_covering
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_slit_preimage_near
import Theorems.Thm_Erdos1041_Counterexample_s3_bottleneck_isCoveringMap
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
/-- The numerical finish, with no rectifiability or continuity assumption. -/
theorem bottleneck_length_of_near_point (γ : ℝ → ℂ) (b₁ b₂ cc : ℂ)
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂) (δ : ℝ) (aHat : ℂ)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hnear : ‖γ τ - cc‖ < 4 / 3 * Real.sqrt (δ / ‖aHat‖)) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ -
      8 / 3 * Real.sqrt (δ / ‖aHat‖)) ≤ pathLength γ := by
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans
    (bottleneck_length_via_point γ b₁ b₂ cc hγ0 hγ1 τ hτ)
end Erdos1041.Counterexample

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (hsimple : Polynomial.rootMultiplicity cc (Polynomial.derivative p) = 1)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (γ : ℝ → ℂ) (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ connectedComponentIn (Omega p) cc) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
      ≤ pathLength γ := by
  have hdeg := bottleneck_natDegree_pos p cc b₁ hv hr₁
  have hcover := s3_bottleneck_isCoveringMap p cc hcc hv hdeg huniq
  obtain ⟨τ, hτ, hmeet⟩ := bottleneck_path_meets_slit_of_covering p cc hv hcover
    b₁ b₂ hne hr₁ hr₂ γ hcont hγ0 hγ1 hγmem
  exact bottleneck_length_of_near_point γ b₁ b₂ cc hγ0 hγ1 δ aHat τ hτ
    (bottleneck_slit_preimage_near p cc hcrit hv hcover aHat haHat h hh hdisk δ hδ
      hδpos hδsmall b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros huniq (γ τ) hmeet.1 hmeet.2)
