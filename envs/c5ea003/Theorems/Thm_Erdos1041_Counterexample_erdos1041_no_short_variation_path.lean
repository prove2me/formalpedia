-- Prove2me | Theorems.Thm_Erdos1041_Counterexample_erdos1041_no_short_variation_path
-- name    : Erdos1041.Counterexample.erdos1041_no_short_variation_path
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:37:45.507891+00:00
-- url     : https://prove2.me/theorems/5fd97c7f-1f1a-4219-bfd8-48a088e568a7
-- title:
--   The universal short-variation assertion is false
-- statement:
--   It is false that every monic complex polynomial of degree n≥2 with all roots in the open unit disc admits two root occurrences and a continuous path between them in |p|<1 whose extended total variation on [0,1] is less than 2. Root occurrences are counted with multiplicity in the statement.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean#L36-L83
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
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

open Erdos1041.Counterexample

theorem Erdos1041.Counterexample.erdos1041_no_short_variation_path :
    ¬ ∀ (n : ℕ) (p : ℂ[X]), n ≥ 2 → p.natDegree = n → p.Monic →
        p.rootSet ℂ ⊆ ball (0 : ℂ) 1 →
        ∃ (z₁ z₂ : ℂ)
          (h : ({z₁, z₂} : Multiset ℂ) ≤ p.roots)
          (γ : ℝ → ℂ),
          ContinuousOn γ (Set.Icc 0 1) ∧
          γ 0 = z₁ ∧ γ 1 = z₂ ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖p.eval (γ τ)‖ < 1) ∧
          eVariationOn γ (Set.Icc 0 1) < (2 : ℝ≥0∞) := by sorry
