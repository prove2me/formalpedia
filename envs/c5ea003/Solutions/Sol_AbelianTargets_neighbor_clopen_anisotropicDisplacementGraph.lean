-- Prove2me | solution 1 for AbelianTargets.neighbor_clopen_anisotropicDisplacementGraph
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:11:50.678831+00:00
-- url     : https://prove2.me/submissions/99eb8575-8261-46ba-ac1d-b4e153da2632

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
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
# Clopen markers at independent coordinate scales

The initial marker construction in Lemma 3.2 is proved for an actual free
continuous action. Each coordinate has its own scale. This is the input
to the later packing, priority, cut, and rectangular subdivision steps.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]

theorem solution (L : Fin d → ℕ)
    (free : IsFree (G := Lattice d) (X := X)) (S : Set X) (hS : IsClopen S) :
    IsClopen (NeighborSet (anisotropicDisplacementGraph L free) S) := by
  have heq : NeighborSet (anisotropicDisplacementGraph L free) S =
      ⋃ g ∈ anisotropicDisplacements L, {y : X | (-g) +ᵥ y ∈ S} := by
    ext y
    constructor
    · rintro ⟨x,hx,g,hg,hxy⟩
      refine Set.mem_iUnion.mpr ⟨g,Set.mem_iUnion.mpr ⟨hg,?_⟩⟩
      change -g +ᵥ y ∈ S
      rw [← hxy,← add_vadd,neg_add_cancel,zero_vadd]
      exact hx
    · intro hy
      obtain ⟨g,hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hg,hy⟩ := Set.mem_iUnion.mp hy
      refine ⟨-g +ᵥ y,hy,g,hg,?_⟩
      rw [← add_vadd,add_neg_cancel,zero_vadd]
  rw [heq]
  apply isClopen_biUnion_finset
  intro g _
  exact hS.preimage (continuous_const_vadd (-g))
