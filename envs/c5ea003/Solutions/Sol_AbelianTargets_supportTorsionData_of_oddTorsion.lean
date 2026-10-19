-- Prove2me | solution 1 for AbelianTargets.supportTorsionData_of_oddTorsion
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:14:41.480383+00:00
-- url     : https://prove2.me/submissions/b7605c9f-eefb-4c12-bd1a-341cd2370e82

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_Nonisolated
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportTorsion
import Definitions.Def_AT260939824_SupportWitness
import Definitions.Def_AT260939824_TopologicalWalks
import Definitions.Def_AbelianTargets260939824ReducedWalks
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Theorems.Thm_AbelianTargets_oddSupportPath_torsion

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.Nonisolated
section
/-!
# Removing isolated target vertices

The nonisolated induced graph has a total neighbor selection.  Retraction
onto it preserves the odd torsion hypotheses of the target paper.
-/

namespace AbelianTargets

noncomputable section

variable {V : Type*} (H : SimpleGraph V)









theorem nonisolatedNeighbor_adj (v : nonisolatedVertices H) :
    (NonisolatedGraph H).Adj v (nonisolatedNeighbor H v) :=
  Classical.choose_spec (nonisolated_neighbor H v)



theorem oddWalk_nonisolated {b : V} (γ : H.Walk b b) (hodd : Odd γ.length) :
    b ∈ nonisolatedVertices H := by
  cases γ with
  | nil => simp only [SimpleGraph.Walk.length_nil] at hodd; exact (Nat.not_odd_zero hodd).elim
  | cons h p => exact ⟨_, h⟩

theorem hasOddTorsion_nonisolated (h : HasOddTorsion H) : HasOddTorsion (NonisolatedGraph H) := by
  obtain ⟨b, γ, hodd, N, hN, hnull⟩ := h
  let b' : nonisolatedVertices H := ⟨b, oddWalk_nonisolated H γ hodd⟩
  let f := nonisolatedRetraction H b'
  exact ⟨f b, γ.map f, by simpa using hodd, N, hN, by
    simpa only [loopPower_map, SimpleGraph.Walk.map_nil] using hnull.map f⟩



end

end AbelianTargets

end

/-!
# Support-space data from an arbitrary odd torsion target

This file removes the intermediate total-neighbor-choice hypothesis.
Every finite graph satisfying the actual odd torsion condition supplies
the two swapped paths and a nullhomotopy of their alternating power.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] (H : SimpleGraph V)

theorem solution (hH : HasOddTorsion H) :
    Nonempty (SupportTorsionData H) := by
  classical
  let J := NonisolatedGraph H
  letI : Fintype (nonisolatedVertices H) := Fintype.ofFinite _
  obtain ⟨a, γ, hodd, N, hN, hnull⟩ := hasOddTorsion_nonisolated H hH
  let s := nonisolatedNeighbor H
  have hs : ∀ v, J.Adj v (s v) := nonisolatedNeighbor_adj H
  let α := oddSupportPath J s hs γ hodd
  let β := swappedReturnPath J α
  obtain ⟨k, hk, hP⟩ := oddSupportPath_torsion J s hs γ hodd hnull
  have hkpos : 0 < k := by omega
  let D : SupportTorsionData J := {
    base := SupportPair.vertex J (hs a)
    a := α
    b := β
    b_swap := fun _ => rfl
    power := k
    power_pos := hkpos
    null_power := hP }
  exact ⟨D.map (SimpleGraph.Embedding.induce (nonisolatedVertices H)).toHom⟩
