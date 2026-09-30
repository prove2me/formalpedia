-- Prove2me | solution 1 for Erdos1041.Counterexample.erdos1041_no_short_variation_path
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-30T01:41:13.405379+00:00
-- url     : https://prove2.me/submissions/da0bb085-94c4-4893-8fba-49dfb8ae2aef

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
    ¬ ∀ (n : ℕ) (p : ℂ[X]), n ≥ 2 → p.natDegree = n → p.Monic →
        p.rootSet ℂ ⊆ ball (0 : ℂ) 1 →
        ∃ (z₁ z₂ : ℂ)
          (h : ({z₁, z₂} : Multiset ℂ) ≤ p.roots)
          (γ : ℝ → ℂ),
          ContinuousOn γ (Set.Icc 0 1) ∧
          γ 0 = z₁ ∧ γ 1 = z₂ ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖p.eval (γ τ)‖ < 1) ∧
          eVariationOn γ (Set.Icc 0 1) < (2 : ℝ≥0∞) := by
  intro huniv
  obtain ⟨hmonic, hdeg, hdisk, hnodup, hvar⟩ := erdos1041_counterexample
  have hn : (7 : ℕ) ≥ 2 := by norm_num
  have hrootset : f.rootSet ℂ ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hzroot : f.IsRoot z := by
      rw [IsRoot, ← coe_aeval_eq_eval]
      exact hmonic.mem_rootSet.mp hz
    simpa [mem_ball, dist_zero_right] using hdisk z hzroot
  obtain ⟨z₁, z₂, hle, γ, hcont, hγ0, hγ1, hmem, hlen⟩ :=
    huniv 7 f hn hdeg hmonic hrootset
  have hz1_mem : z₁ ∈ f.roots := by
    have hpos : 0 < ({z₁, z₂} : Multiset ℂ).count z₁ := by
      simp [Multiset.count_singleton]
    exact Multiset.count_pos.mp
      (lt_of_lt_of_le hpos ((Multiset.le_iff_count.mp hle) z₁))
  have hz2_mem : z₂ ∈ f.roots := by
    have hpos : 0 < ({z₁, z₂} : Multiset ℂ).count z₂ := by
      simp [Multiset.count_cons]
    exact Multiset.count_pos.mp
      (lt_of_lt_of_le hpos ((Multiset.le_iff_count.mp hle) z₂))
  have hz1 : f.IsRoot z₁ := (mem_roots hmonic.ne_zero).mp hz1_mem
  have hz2 : f.IsRoot z₂ := (mem_roots hmonic.ne_zero).mp hz2_mem
  have hne : z₁ ≠ z₂ := by
    intro heq
    have htwo : 2 ≤ f.roots.count z₁ := by
      have hpair : ({z₁, z₂} : Multiset ℂ).count z₁ = 2 := by
        simp [heq]
      exact hpair ▸ (Multiset.le_iff_count.mp hle) z₁
    have hone : f.roots.count z₁ ≤ 1 :=
      (Multiset.nodup_iff_count_le_one.mp hnodup) z₁
    exact (Nat.not_succ_le_self 1) (le_trans htwo hone)
  have hgt : (2 : ℝ≥0∞) < eVariationOn γ (Set.Icc 0 1) := by
    simpa only [pathLength] using hvar z₁ z₂ hz1 hz2 hne γ hcont hγ0 hγ1 hmem
  exact lt_asymm hgt hlen
