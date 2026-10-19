-- Prove2me | Definitions.Def_AT260939824_CarrierSupportProjection
-- name    : AT260939824_CarrierSupportProjection
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:31:08.340425+00:00
-- url     : https://prove2.me/theorems/e548edbc-1e25-4611-86ab-03ae204fbfd2
-- title:
--   Projection of the interval carrier to graph support pairs
-- statement:
--   Let $D$ be support-torsion data for a finite graph $H$, with odd base $m=2q+1$. The skeleton formula is continuous on each singleton, each horizontal graph-edge face, and each vertical graph-edge face. Whole relation-cell charts restrict to that same formula wherever the probability support lies in the graph skeleton.
--
--   These facts assemble compatible projection charts for every height $K$ and integer interval $[A,B]$, yielding a map
--
--   $$\mathcal C_m^K([A,B])\longrightarrow\operatorname{SupportPair}(H).$$
--
--   The construction uses the supplied path and relation homotopy in $D$. The selected support-conversion lemmas identify raw carrier vertices with the corresponding subtype vertices when passing between cell and face descriptions.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4, 7.1; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/CarrierSupportProjection.lean, selected declaration lines 12-17, 19-28, 35-39, 41-50, 52-57, 59-87, 89-119, 121-123; SHA-256 f4c3fbacea0c518b8792f12cac4c386e7f0d4d49723a54143a40c9a51ff6e667. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_EquivariantCellCharts
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_ParitySwapGeometry
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_ProbabilityTwoVertices
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportCellRestrictions
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportSkeletonMap
import Definitions.Def_AT260939824_SupportWitness
import Definitions.Def_AT260939824_TopologicalWalks
import Definitions.Def_AT260939824_TriangleChartIntersections
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

/-! The actual continuous carrier projection supplied by odd torsion. -/
namespace AbelianTargets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped unitInterval

namespace IntervalCarriers
theorem rawSupported_singleton {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B))
    (u : Vertex) (hu : u∈carrierVertices K A B) (hp : RawSupported p {u}) :
    p.SupportedOn ({⟨u,hu⟩}:Set (CarrierVertex K A B)) := by
  intro v hv
  apply Subtype.ext
  exact Finset.mem_singleton.mp (hp v hv)

theorem rawSupported_pair {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B))
    (u v : Vertex) (hu : u∈carrierVertices K A B) (hv : v∈carrierVertices K A B)
    (hp : RawSupported p {u,v}) :
    p.SupportedOn ({⟨u,hu⟩,⟨v,hv⟩}:Set (CarrierVertex K A B)) := by
  intro w hw
  have hs := hp w hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with hs | hs
  · exact Or.inl (Subtype.ext hs)
  · exact Or.inr (Subtype.ext hs)
end IntervalCarriers

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]

theorem continuousOn_skeletonMap_singleton (f : V → IntervalCarriers.Vertex) (v : V) :
    ContinuousOn (D.skeletonMap f) {p | p.SupportedOn ({v}:Set V)} := by
  apply (continuous_const : Continuous (fun _:Probability V => SupportPair.paritySwap H (f v).1 D.base)).continuousOn.congr
  intro p hp
  exact D.skeletonMap_singleton f p v hp

theorem continuousOn_skeletonMap_horizontal (f : V → IntervalCarriers.Vertex) (u v : V)
    (he : IntervalCarriers.HorizontalStep (2*D.power+1) (f u) (f v)) :
    ContinuousOn (D.skeletonMap f) {p | p.SupportedOn ({u,v}:Set V)} := by
  have hc : Continuous (fun p:Probability V => SupportPair.paritySwap H (f u).1
      (D.a ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩)) :=
    (SupportPair.continuous_paritySwap H _).comp
      (D.a.continuous.comp ((Probability.continuous_mass_apply v).subtype_mk _))
  apply hc.continuousOn.congr
  intro p hp
  exact D.skeletonMap_horizontal f p u v hp he

theorem continuousOn_skeletonMap_vertical (f : V → IntervalCarriers.Vertex) (u v : V)
    (he : (f u).1=(f v).1) :
    ContinuousOn (D.skeletonMap f) {p | p.SupportedOn ({u,v}:Set V)} := by
  apply (continuous_const : Continuous (fun _:Probability V => SupportPair.paritySwap H (f u).1 D.base)).continuousOn.congr
  intro p hp
  exact D.skeletonMap_vertical f p u v hp he

theorem cellChart_supported_skeleton_pair (f : V → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (s : Finset IntervalCarriers.Vertex)
    (hs : IntervalCarriers.IsFanTriangle (2*D.power+1) c s)
    (p : Probability V) (hps : ∀v,0<p.mass v→f v∈s) (u v : V)
    (hp : p.SupportedOn ({u,v}:Set V))
    (he : (IntervalCarriers.graph (2*D.power+1)).Adj (f u) (f v)) :
    D.cellChart f c p=D.skeletonMap f p := by
  by_cases hu : 0<p.mass u
  · by_cases hv : 0<p.mass v
    · exact D.cellChart_supported_pair f c s hs p u v hp (hps u hu) (hps v hv) he
    · have hz : p.mass v=0 := le_antisymm (le_of_not_gt hv) (p.nonneg v)
      have hp' : p.SupportedOn ({u}:Set V) := by
        intro w hw
        rcases hp w hw with rfl | rfl
        · rfl
        · simp [hz] at hw
      rw [D.skeletonMap_singleton f p u hp',p.eq_dirac_of_singleton u hp']
      exact D.cellChart_vertex f c s hs u (hps u hu)
  · have hz : p.mass u=0 := le_antisymm (le_of_not_gt hu) (p.nonneg u)
    have hp' : p.SupportedOn ({v}:Set V) := by
      intro w hw
      rcases hp w hw with rfl | rfl
      · simp [hz] at hw
      · rfl
    have hv : f v∈s := by
      have hpv : p.mass v=1 := by rw [p.eq_dirac_of_singleton v hp']; simp
      exact hps v (by rw [hpv]; norm_num)
    rw [D.skeletonMap_singleton f p v hp',p.eq_dirac_of_singleton v hp']
    exact D.cellChart_vertex f c s hs v hv

def projectionCharts (K : ℕ) (A B : ℤ) :
    IntervalCarriers.CarrierProjectionCharts (2*D.power+1) K A B (SupportPair H) where
  skeleton := D.skeletonMap Subtype.val
  continuous_vertex u hu := by
    exact (D.continuousOn_skeletonMap_singleton Subtype.val ⟨u,hu⟩).mono
      (fun p hp => IntervalCarriers.rawSupported_singleton p u hu hp)
  continuous_edge u hu v hv he := by
    let u' : IntervalCarriers.CarrierVertex K A B := ⟨u,hu⟩
    let v' : IntervalCarriers.CarrierVertex K A B := ⟨v,hv⟩
    have hp : ∀p,IntervalCarriers.RawSupported p {u,v}→p.SupportedOn ({u',v'}:Set _) :=
      fun p hp => IntervalCarriers.rawSupported_pair p u v hu hv hp
    rcases he with ⟨_,he | he⟩ <;> rcases he with he | he
    · exact (D.continuousOn_skeletonMap_horizontal Subtype.val u' v' he).mono (fun p h => hp p h)
    · exact (D.continuousOn_skeletonMap_vertical Subtype.val u' v'
        (by change u.1=v.1; change v=(u.1,u.2+1) at he; rw [he])).mono (fun p h => hp p h)
    · have hrev := (D.continuousOn_skeletonMap_horizontal Subtype.val v' u' he)
      exact hrev.mono (fun p h => by simpa [Set.pair_comm] using hp p h)
    · exact (D.continuousOn_skeletonMap_vertical Subtype.val u' v'
        (by change u.1=v.1; change u=(v.1,v.2+1) at he; rw [he])).mono (fun p h => hp p h)
  cell := D.cellChart Subtype.val
  continuous_cell c hc := D.continuous_cellChart _ c
  cell_skeleton c hc t ht p hpt hsk := by
    rcases hsk with ⟨v,hv,hp⟩ | ⟨u,hu,v,hv,he,hp⟩
    · have hp' := IntervalCarriers.rawSupported_singleton p v hv hp
      have hv' : v∈t := by
        have hmass : p.mass ⟨v,hv⟩=1 := by rw [p.eq_dirac_of_singleton ⟨v,hv⟩ hp']; simp
        exact hpt ⟨v,hv⟩ (by rw [hmass]; norm_num)
      rw [D.skeletonMap_singleton Subtype.val p ⟨v,hv⟩ hp',p.eq_dirac_of_singleton ⟨v,hv⟩ hp']
      exact D.cellChart_vertex (Subtype.val : IntervalCarriers.CarrierVertex K A B → _) c t ht ⟨v,hv⟩ hv'
    · exact D.cellChart_supported_skeleton_pair _ c t ht p hpt ⟨u,hu⟩ ⟨v,hv⟩
        (IntervalCarriers.rawSupported_pair p u v hu hv hp) he

def carrierProjection (K : ℕ) (A B : ℤ) :
    IntervalCarriers.Realization (2*D.power+1) K A B → SupportPair H :=
  (D.projectionCharts K A B).eval (by omega)



end SupportTorsionData
end
end AbelianTargets


