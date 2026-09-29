-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_covering_fibre_eq_on_preconnected
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:04.042438+00:00
-- url     : https://prove2.me/submissions/ac639729-98f3-47db-8509-0fc755c4a2c2

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
theorem solution
    {E B T : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace B] [TopologicalSpace T]
    [SimplyConnectedSpace B] [LocPathConnectedSpace B]
    (π : E → B) (hπ : IsCoveringMap π)
    (S : Set T) (hS : IsPreconnected S) (g : T → E) (hg : ContinuousOn g S)
    (a b : T) (ha : a ∈ S) (hb : b ∈ S) (hab : π (g a) = π (g b)) :
    g a = g b := by
  obtain ⟨σ, ⟨hσa, hσπ⟩, -⟩ :=
    hπ.existsUnique_continuousMap_lifts (ContinuousMap.id B) (π (g a)) (g a) rfl
  have hsection (y : B) : π (σ y) = y := congrFun hσπ y
  have hsecond : ContinuousOn (fun t => σ (π (g t))) S :=
    σ.continuous.comp_continuousOn (hπ.continuous.comp_continuousOn hg)
  have heq : S.EqOn g (fun t => σ (π (g t))) :=
    (T2Space.isSeparatedMap π).eqOn_of_comp_eqOn
      hπ.isLocalHomeomorph.isLocallyInjective hS hg hsecond
      (fun t _ => (hsection (π (g t))).symm) ha hσa.symm
  calc
    g a = σ (π (g a)) := hσa.symm
    _ = σ (π (g b)) := congrArg σ hab
    _ = g b := (heq hb).symm
