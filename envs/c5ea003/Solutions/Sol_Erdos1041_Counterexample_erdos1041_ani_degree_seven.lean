-- Prove2me | solution 1 for Erdos1041.Counterexample.erdos1041_ani_degree_seven
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-30T01:41:11.990061+00:00
-- url     : https://prove2.me/submissions/524adea1-6c7f-4e2d-8d44-1c878c82a29f

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Theorems.Thm_Erdos1041_Counterexample_erdos1041_counterexample
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

/-!
Catalogue-shaped adapters for the Formal Conjectures 1041 contribution.

These theorems are the logical and multiset interface between
`erdos1041_counterexample` and the repaired total-variation parent. They do
not formalise a Hausdorff-measure comparison, and they do not assert ani's
small-parameter family theorem.

The mathematics is ani's. The Formal Conjectures parent should not carry a
`formal_proof` annotation until a checked public permalink of
`erdos1041_no_short_variation_path` exists.
-/

noncomputable section

open scoped ENNReal
open Polynomial Metric

open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution :
    ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) →
          γ 0 = z₁ → γ 1 = z₂ →
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖p.eval (γ τ)‖ < 1) →
          (2 : ℝ≥0∞) < eVariationOn γ (Set.Icc 0 1) := by
  refine ⟨f, ?_⟩
  simpa only [pathLength] using erdos1041_counterexample
