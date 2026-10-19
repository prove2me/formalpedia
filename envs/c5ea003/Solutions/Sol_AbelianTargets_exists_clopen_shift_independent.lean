-- Prove2me | solution 1 for AbelianTargets.exists_clopen_shift_independent
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:11:27.001846+00:00
-- url     : https://prove2.me/submissions/79895c0e-d29e-4cd7-9fae-da79217fb73f

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Existence of clopen separated covering orbit markers

This file completes the positive membership of the concrete graph in
Lemma 7.3. A countable clopen independent cover is built from freeness,
zero-dimensionality, and second countability. The greedy clopen maximal
independent set then supplies the required orbit markers.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
universe u
variable {d L : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]
variable [T1Space X]

theorem solution
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X))
    (x : X) (g : Lattice d) (hg : g ≠ 0) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ y ∈ U, g +ᵥ y ∉ U := by
  have hxg : x ≠ g +ᵥ x := by
    intro h
    exact hg (free g x h.symm)
  obtain ⟨B, hB, hxB, hBsub⟩ := zeroDim.exists_subset_of_mem_open
    (show x ∈ ({g +ᵥ x} : Set X)ᶜ by simpa using hxg)
    isClosed_singleton.isOpen_compl
  have hgB : g +ᵥ x ∉ B := by
    intro h
    exact hBsub h (Set.mem_singleton _)
  refine ⟨B ∩ (fun y : X => g +ᵥ y) ⁻¹' Bᶜ,
    hB.inter (hB.compl.preimage (continuous_const_vadd g)), ⟨hxB, hgB⟩, ?_⟩
  intro y hy hgy
  exact hy.2 hgy.1
