-- Prove2me | solution 1 for Erdos1041.Counterexample.s2_covering_injective
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:31:48.106229+00:00
-- url     : https://prove2.me/submissions/3fe4b8b2-2b9c-4362-8980-100b5dac1bdc

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
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

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Formalisation of Lemma 2.1 from `ani_degree7_counterexample.tex`. -/

/-
Integration: move the S2 declaration out of Defs before importing this module.
The supplied Defs is preserved under input/; see DEFS_DELTAS.md.
Repaired and compiled against Mathlib v4.29.1 (commit 5e932f97).
-/

noncomputable section

open Set Filter Topology

open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    {g : E → X} (hcover : IsCoveringMap g) : Function.Injective g := by
  intro a b hab
  obtain ⟨σ, hσ, _⟩ := hcover.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) (g a) a rfl
  have hcomp : g ∘ (σ ∘ g) = g ∘ (id : E → E) := by
    funext e
    exact congrFun hσ.2 (g e)
  have hleft : (σ : X → E) ∘ g = (id : E → E) :=
    hcover.eq_of_comp_eq (σ.continuous.comp hcover.continuous)
      continuous_id hcomp a hσ.1
  calc
    a = σ (g a) := (congrFun hleft a).symm
    _ = σ (g b) := congrArg σ hab
    _ = b := congrFun hleft b
