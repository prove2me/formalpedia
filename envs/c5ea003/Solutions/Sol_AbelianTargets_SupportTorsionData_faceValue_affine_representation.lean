-- Prove2me | solution 1 for AbelianTargets.SupportTorsionData.faceValue_affine_representation
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:09:16.392992+00:00
-- url     : https://prove2.me/submissions/a060c006-4e20-49cf-83bf-526841448d1e

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CarrierSupportProjection
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_ParitySwapGeometry
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportCellCharts
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportRelationCharts
import Definitions.Def_AT260939824_SupportSkeletonMap
import Definitions.Def_AT260939824_SupportWitness
import Definitions.Def_AT260939824_TopologicalWalks
import Definitions.Def_AT260939824_TriangleChartIntersections
import Definitions.Def_AT260939824_UniformAffineSupportCharts
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

-- Preserved source skeleton: AbelianTargets.UniformAffineSupportCharts
section
/-! A common modulus for all torsion charts, independent of the vertex set. -/
universe v
namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace SupportPair

end SupportPair

namespace Probability

theorem parameter_indicator {V : Type*} [Fintype V] (p : Probability V) (v : V) :
    parameter (unitIndicator v) p=
      ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩ := by
  classical
  apply Subtype.ext
  unfold unitIndicator
  change (∑w,p.mass w*↑(if w=v then (1:I) else 0))=p.mass v
  calc
    _ = ∑w,if w=v then p.mass w else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases h:w=v <;> simp [h]
    _ = _ := by simp
end Probability

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)



theorem affineChart_bottom_constant {V : Type*} [Fintype V] (p:Probability V) :
    D.affineChart (fun _ => 0) (fun _ => 0) p=D.base := by
  unfold affineChart
  simp only [Probability.parameter_const,Path.Homotopy.source]

theorem affineChart_top_indicator {V : Type*} [Fintype V] (p:Probability V) (v:V) :
    D.affineChart (fun _ => 1) (Probability.unitIndicator v) p=
      D.a ⟨p.mass v,p.nonneg v,p.mass_le_one v⟩ := by
  classical
  unfold affineChart
  rw [Probability.parameter_const,Probability.parameter_indicator,D.relationHomotopy.apply_one]
  rfl

end SupportTorsionData
end
end AbelianTargets

end

namespace AbelianTargets.SupportTorsionData
end AbelianTargets.SupportTorsionData
open AbelianTargets
open AbelianTargets.SupportTorsionData
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
open IntervalCarriers

theorem solution (K : ℕ) (A B : ℤ) (s : Finset (CarrierVertex K A B))
    (hs : s∈simplexFaces (2*D.power+1) K A B) :
    ∃ (r:ℤ) (height theta:CarrierVertex K A B→I),
      ∀p:Probability (CarrierVertex K A B),p.SupportedOn (s:Set _)→
        (D.projectionCharts K A B).faceValue s p=
          SupportPair.paritySwap H r (D.affineChart height theta p) := by
  by_cases hc : FaceHasCell (m:=2*D.power+1) s
  · refine ⟨hc.choose.1,cellHeight hc.choose∘Subtype.val,
      cellTheta D.power (2*D.power+1) hc.choose∘Subtype.val,?_⟩
    intro p hp
    rw [CarrierProjectionCharts.faceValue,dif_pos hc]
    rfl
  · rcases (mem_simplexFaces s).mp hs with ⟨v,hv,hsub⟩ | ⟨u,hu,v,hv,he,hsub⟩ | ⟨t,ht,hsub⟩
    · refine ⟨v.1,(fun _=>0),(fun _=>0),?_⟩
      intro p hp
      rw [CarrierProjectionCharts.faceValue,dif_neg hc]
      change D.skeletonMap Subtype.val p= _
      rw [D.skeletonMap_singleton Subtype.val p ⟨v,hv⟩
        (rawSupported_singleton p v hv ((rawSupported_of_face hp).mono hsub)),
        D.affineChart_bottom_constant]
    · let u' : CarrierVertex K A B := ⟨u,hu⟩
      let v' : CarrierVertex K A B := ⟨v,hv⟩
      have hp : ∀p:Probability (CarrierVertex K A B),p.SupportedOn (s:Set _)→
          p.SupportedOn ({u',v'}:Set _) := fun p h =>
        rawSupported_pair p u v hu hv ((rawSupported_of_face h).mono hsub)
      rcases he with ⟨_,he | he⟩ <;> rcases he with he | he
      · refine ⟨u.1,(fun _=>1),Probability.unitIndicator v',?_⟩
        intro p h
        rw [CarrierProjectionCharts.faceValue,dif_neg hc]
        change D.skeletonMap Subtype.val p= _
        rw [D.skeletonMap_horizontal Subtype.val p u' v' (hp p h) he,D.affineChart_top_indicator]
      · refine ⟨u.1,(fun _=>0),(fun _=>0),?_⟩
        intro p h
        rw [CarrierProjectionCharts.faceValue,dif_neg hc]
        change D.skeletonMap Subtype.val p= _
        have hh : u.1=v.1 := by change v=(u.1,u.2+1) at he; rw [he]
        rw [D.skeletonMap_vertical Subtype.val p u' v' (hp p h) hh,D.affineChart_bottom_constant]
      · refine ⟨v.1,(fun _=>1),Probability.unitIndicator u',?_⟩
        intro p h
        rw [CarrierProjectionCharts.faceValue,dif_neg hc]
        change D.skeletonMap Subtype.val p= _
        have hp' : p.SupportedOn ({v',u'}:Set _) := by simpa [Set.pair_comm] using hp p h
        rw [D.skeletonMap_horizontal Subtype.val p v' u' hp' he,D.affineChart_top_indicator]
      · refine ⟨u.1,(fun _=>0),(fun _=>0),?_⟩
        intro p h
        rw [CarrierProjectionCharts.faceValue,dif_neg hc]
        change D.skeletonMap Subtype.val p= _
        have hh : u.1=v.1 := by change u=(v.1,v.2+1) at he; rw [he]
        rw [D.skeletonMap_vertical Subtype.val p u' v' (hp p h) hh,D.affineChart_bottom_constant]
    · obtain ⟨c,hc',hct⟩ := fanTriangle_of_carrierTriangle ht
      exact False.elim (hc ⟨c,hc',t,hct,hsub⟩)
