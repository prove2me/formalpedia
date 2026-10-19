-- Prove2me | solution 1 for AbelianTargets.SupportTorsionData.carrierProjection_push_same
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T03:55:00.257177+00:00
-- url     : https://prove2.me/submissions/ed7cc2e5-6dd8-4247-8ac0-fa55f623782a

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CarrierProjectionNaturality
import Definitions.Def_AT260939824_CarrierSupportProjection
import Definitions.Def_AT260939824_CarrierTriangulation
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
import Theorems.Thm_AbelianTargets_IntervalCarriers_CarrierProjectionCharts_eval_eq_cell
import Theorems.Thm_AbelianTargets_Probability_minimumCoordinate_push
import Theorems.Thm_AbelianTargets_Probability_parameter_push

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.SupportChartNaturality
section
set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets
noncomputable section
open scoped BigOperators unitInterval
attribute [local instance] Classical.propDecidable

namespace Probability
variable {V W : Type*} [Fintype V] [Fintype W]









end Probability

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V U : Type*} [Fintype V] [Fintype U]

theorem rawCellChart_push (f : V → U) (g : U → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (p : Probability V) :
    D.rawCellChart g c (Probability.push f p)=D.rawCellChart (g ∘ f) c p := by
  unfold rawCellChart affineChart
  rw [Probability.parameter_push,Probability.parameter_push]
  rfl

theorem cellChart_push (f : V → U) (g : U → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (p : Probability V) :
    D.cellChart g c (Probability.push f p)=D.cellChart (g ∘ f) c p := by
  unfold cellChart
  rw [D.rawCellChart_push]

theorem skeletonMap_push (f : V → U) (g : U → IntervalCarriers.Vertex)
    (p : Probability V) : D.skeletonMap g (Probability.push f p)=D.skeletonMap (g ∘ f) p := by
  unfold skeletonMap
  rw [Probability.minimumCoordinate_push]
  dsimp only
  rw [Probability.parameter_push]
  rfl







end SupportTorsionData
end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.CarrierProjectionNaturality
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
attribute [local instance] Classical.propDecidable

namespace IntervalCarriers

theorem realization_skeleton_or_cell {m K : ℕ} {A B : ℤ} (p : Realization m K A B) :
    SkeletonSupported (m := m) p.1 ∨
      ∃ c∈carrierCells m K A B,∃ t,IsFanTriangle m c t ∧ RawSupported p.1 t := by
  obtain ⟨s,hs,hp⟩ := p.2
  have hr := rawSupported_of_face hp
  rcases (mem_simplexFaces s).mp hs with ⟨v,hv,hsub⟩ | ⟨u,hu,v,hv,he,hsub⟩ | ⟨t,ht,hsub⟩
  · exact Or.inl (Or.inl ⟨v,hv,hr.mono hsub⟩)
  · exact Or.inl (Or.inr ⟨u,hu,v,hv,he,hr.mono hsub⟩)
  · obtain ⟨c,hc,hct⟩ := fanTriangle_of_carrierTriangle ht
    exact Or.inr ⟨c,hc,t,hct,hr.mono hsub⟩

theorem RawSupported.push_same {K T : ℕ} {A B C D : ℤ}
    (f : CarrierVertex K A B → CarrierVertex T C D)
    (hf : ∀v,(f v).1=v.1) {p : Probability (CarrierVertex K A B)}
    {s : Finset Vertex} (hp : RawSupported p s) : RawSupported (Probability.push f p) s := by
  intro w hw
  obtain ⟨v,hv,hpv⟩ := (Probability.push_pos_iff f p w).mp hw
  rw [←hv,hf]
  exact hp v hpv

theorem SkeletonSupported.push_same {m K T : ℕ} {A B C D : ℤ}
    (f : CarrierVertex K A B → CarrierVertex T C D)
    (hf : ∀v,(f v).1=v.1) {p : Probability (CarrierVertex K A B)}
    (hp : SkeletonSupported (m := m) p) : SkeletonSupported (m := m) (Probability.push f p) := by
  have hm : ∀v∈carrierVertices K A B,v∈carrierVertices T C D := by
    intro v hv
    have h := (f ⟨v,hv⟩).2
    simpa only [hf] using h
  rcases hp with ⟨v,hv,hp⟩ | ⟨u,hu,v,hv,he,hp⟩
  · exact Or.inl ⟨v,hm v hv,hp.push_same f hf⟩
  · exact Or.inr ⟨u,hm u hu,v,hm v hv,he,hp.push_same f hf⟩







end IntervalCarriers

namespace SupportTorsionData
open IntervalCarriers
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)











end SupportTorsionData
end
end AbelianTargets

end

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
attribute [local instance] Classical.propDecidable
namespace AbelianTargets.SupportTorsionData
end AbelianTargets.SupportTorsionData
open AbelianTargets
open AbelianTargets.SupportTorsionData
open IntervalCarriers
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)

theorem solution {K T : ℕ} {A B C E : ℤ}
    (f : CarrierVertex K A B → CarrierVertex T C E) (hf : ∀v,(f v).1=v.1)
    (hc : carrierCells (2*D.power+1) K A B ⊆ carrierCells (2*D.power+1) T C E)
    (i : Realization (2*D.power+1) K A B → Realization (2*D.power+1) T C E)
    (hi : ∀p,(i p).1=Probability.push f p.1)
    (p : Realization (2*D.power+1) K A B) : D.carrierProjection T C E (i p)=D.carrierProjection K A B p := by
  have hf' : (Subtype.val : CarrierVertex T C E → Vertex) ∘ f=Subtype.val := by funext v; exact hf v
  rcases realization_skeleton_or_cell p with hsk | ⟨c,hc',t,ht,hpt⟩
  · have hsk' : SkeletonSupported (m := 2*D.power+1) (i p).1 := by
      rw [hi]
      exact hsk.push_same f hf
    rw [carrierProjection,(D.projectionCharts T C E).eval_eq_skeleton (by omega) _ hsk']
    rw [carrierProjection,(D.projectionCharts K A B).eval_eq_skeleton (by omega) _ hsk]
    change D.skeletonMap Subtype.val (i p).1=D.skeletonMap Subtype.val p.1
    rw [hi,D.skeletonMap_push,hf']
  · have hpt' : RawSupported (i p).1 t := by rw [hi]; exact hpt.push_same f hf
    rw [carrierProjection,(D.projectionCharts T C E).eval_eq_cell (by omega) _ c (hc hc') t ht hpt']
    rw [carrierProjection,(D.projectionCharts K A B).eval_eq_cell (by omega) _ c hc' t ht hpt]
    change D.cellChart Subtype.val c (i p).1=D.cellChart Subtype.val c p.1
    rw [hi,D.cellChart_push,hf']
