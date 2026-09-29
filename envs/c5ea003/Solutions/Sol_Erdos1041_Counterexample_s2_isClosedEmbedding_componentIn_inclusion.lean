-- Prove2me | solution 1 for Erdos1041.Counterexample.s2_isClosedEmbedding_componentIn_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:05.964492+00:00
-- url     : https://prove2.me/submissions/f2d5d559-89af-4184-b071-69f217fbb01d

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
    {E : Type*} [TopologicalSpace E] {S : Set E} {z : E} (hz : z ∈ S) :
    IsClosedEmbedding (Set.inclusion (connectedComponentIn_subset S z)) := by
  let U : Set E := connectedComponentIn S z
  let ι : U → S := Set.inclusion (connectedComponentIn_subset S z)
  have hrange : Set.range ι = connectedComponent (⟨z, hz⟩ : S) := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      have hu : u.val ∈ connectedComponentIn S z := u.property
      rw [connectedComponentIn_eq_image hz] at hu
      obtain ⟨v, hv, hvu⟩ := hu
      have heq : v = ι u := Subtype.ext hvu
      exact heq ▸ hv
    · intro hv
      have hvU : v.val ∈ U := by
        change v.val ∈ connectedComponentIn S z
        rw [connectedComponentIn_eq_image hz]
        exact ⟨v, hv, rfl⟩
      exact ⟨⟨v.val, hvU⟩, rfl⟩
  refine ⟨IsEmbedding.inclusion (connectedComponentIn_subset S z), ?_⟩
  change IsClosed (Set.range ι)
  rw [hrange]
  exact isClosed_connectedComponent
