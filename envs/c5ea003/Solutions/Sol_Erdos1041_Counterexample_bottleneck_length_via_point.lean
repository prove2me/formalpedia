-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_length_via_point
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:06.687029+00:00
-- url     : https://prove2.me/submissions/5ad0c03a-3553-45d4-a8a0-3c53ad0e719a

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
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

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (γ : ℝ → ℂ) (b₁ b₂ cc : ℂ)
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 2 * ‖γ τ - cc‖) ≤ pathLength γ := by
  have hleft : ENNReal.ofReal ‖b₁ - γ τ‖ ≤ eVariationOn γ (Set.Icc 0 τ) := by
    simpa only [edist_dist, dist_eq_norm, hγ0] using
      eVariationOn.edist_le γ (show (0 : ℝ) ∈ Set.Icc 0 τ from ⟨le_rfl, hτ.1⟩)
        (show τ ∈ Set.Icc 0 τ from ⟨hτ.1, le_rfl⟩)
  have hright : ENNReal.ofReal ‖b₂ - γ τ‖ ≤ eVariationOn γ (Set.Icc τ 1) := by
    simpa only [edist_dist, dist_eq_norm, hγ1] using
      eVariationOn.edist_le γ (show (1 : ℝ) ∈ Set.Icc τ 1 from ⟨hτ.2, le_rfl⟩)
        (show τ ∈ Set.Icc τ 1 from ⟨le_rfl, hτ.2⟩)
  have hsplit : eVariationOn γ (Set.Icc 0 τ) + eVariationOn γ (Set.Icc τ 1) =
      pathLength γ := by
    simpa only [Set.univ_inter, pathLength] using
      eVariationOn.Icc_add_Icc γ (s := Set.univ) hτ.1 hτ.2 (Set.mem_univ τ)
  have hsum : ENNReal.ofReal (‖b₁ - γ τ‖ + ‖b₂ - γ τ‖) ≤ pathLength γ := by
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact (add_le_add hleft hright).trans_eq hsplit
  have htri₁ := norm_add_le (b₁ - γ τ) (γ τ - cc)
  have htri₂ := norm_add_le (b₂ - γ τ) (γ τ - cc)
  have heq₁ : b₁ - γ τ + (γ τ - cc) = b₁ - cc := by ring
  have heq₂ : b₂ - γ τ + (γ τ - cc) = b₂ - cc := by ring
  rw [heq₁] at htri₁
  rw [heq₂] at htri₂
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hsum
