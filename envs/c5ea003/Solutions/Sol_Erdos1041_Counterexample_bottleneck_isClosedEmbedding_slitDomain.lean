-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_isClosedEmbedding_slitDomain
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:30:27.70928+00:00
-- url     : https://prove2.me/submissions/82e1c3a9-e58d-4ece-b1fd-6832de3586f6

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_s2_isClosedEmbedding_componentIn_inclusion
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
theorem solution (p : Polynomial ℂ) (cc : ℂ)
    (hcc : cc ∈ Omega p) :
    IsClosedEmbedding (Set.inclusion (bottleneckSlitDomain_subset p cc)) := by
  refine ⟨IsEmbedding.inclusion (bottleneckSlitDomain_subset p cc), ?_⟩
  have hcomp : Continuous (fun x :
      ((fun z => p.eval z) ⁻¹' bottleneckSlitBase (p.eval cc)) =>
        (⟨(x : ℂ), x.2.1⟩ : Omega p)) :=
    continuous_subtype_val.subtype_mk _
  have hUclosed : IsClosed
      {y : Omega p | (y : ℂ) ∈ connectedComponentIn (Omega p) cc} := by
    have := (s2_isClosedEmbedding_componentIn_inclusion hcc).isClosed_range
    rwa [Set.range_inclusion] at this
  have hset : Set.range (Set.inclusion (bottleneckSlitDomain_subset p cc)) =
      (fun x : ((fun z => p.eval z) ⁻¹' bottleneckSlitBase (p.eval cc)) =>
        (⟨(x : ℂ), x.2.1⟩ : Omega p)) ⁻¹'
        {y : Omega p | (y : ℂ) ∈ connectedComponentIn (Omega p) cc} := by
    rw [Set.range_inclusion]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2.2⟩⟩
  rw [hset]
  exact hUclosed.preimage hcomp
