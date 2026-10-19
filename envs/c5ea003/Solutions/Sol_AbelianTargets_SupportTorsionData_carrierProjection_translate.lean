-- Prove2me | solution 1 for AbelianTargets.SupportTorsionData.carrierProjection_translate
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T03:55:10.31822+00:00
-- url     : https://prove2.me/submissions/893ccb17-8093-4117-b123-57982436d0aa

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CarrierProjectionNaturality
import Definitions.Def_AT260939824_CarrierSupportProjection
import Definitions.Def_AT260939824_CarrierTranslationGeometry
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

-- Preserved source skeleton: AbelianTargets.SupportCellCharts
section
/-! A single continuous chart on each complete literal relation polygon. -/

namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace IntervalCarriers












theorem cellHeight_translate (a : ℤ) (c v : Vertex) :
    cellHeight (translate a c) (translate a v)=cellHeight c v := rfl
theorem cellTheta_translate (a : ℤ) (k m : ℕ) (c v : Vertex) :
    cellTheta k m (translate a c) (translate a v)=cellTheta k m c v := by
  simp [cellTheta,translate,add_sub_add_right_eq_sub]
end IntervalCarriers

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
variable {V : Type*} [Fintype V]













end SupportTorsionData
end
end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.SupportChartNaturality
section
set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets
noncomputable section
open scoped BigOperators unitInterval
attribute [local instance] Classical.propDecidable

namespace Probability
variable {V W : Type*} [Fintype V] [Fintype W]







theorem minimumCoordinate_add (c : V → ℤ) (p : Probability V) (a : ℤ) :
    minimumCoordinate (fun v => c v+a) p=minimumCoordinate c p+a := by
  apply le_antisymm
  · obtain ⟨v,hv,he⟩ := minimumCoordinate_mem c p
    have h := minimumCoordinate_le (fun v => c v+a) p v hv
    simpa only [he] using h
  · obtain ⟨v,hv,he⟩ := minimumCoordinate_mem (fun v => c v+a) p
    have h := minimumCoordinate_le c p v hv
    omega

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

theorem rawCellChart_translate (f : V → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (a : ℤ) (p : Probability V) :
    D.rawCellChart (IntervalCarriers.translate a ∘ f) (IntervalCarriers.translate a c) p=
      D.rawCellChart f c p := by
  unfold rawCellChart
  have hh : IntervalCarriers.cellHeight (IntervalCarriers.translate a c) ∘ (IntervalCarriers.translate a ∘ f)=
      IntervalCarriers.cellHeight c ∘ f := by
    funext v
    exact IntervalCarriers.cellHeight_translate a c (f v)
  have ht : IntervalCarriers.cellTheta D.power (2*D.power+1) (IntervalCarriers.translate a c) ∘
      (IntervalCarriers.translate a ∘ f)=IntervalCarriers.cellTheta D.power (2*D.power+1) c ∘ f := by
    funext v
    exact IntervalCarriers.cellTheta_translate a _ _ c (f v)
  rw [hh,ht]

theorem cellChart_translate (f : V → IntervalCarriers.Vertex)
    (c : IntervalCarriers.Vertex) (a : ℤ) (p : Probability V) :
    D.cellChart (IntervalCarriers.translate a ∘ f) (IntervalCarriers.translate a c) p=
      SupportPair.paritySwap H a (D.cellChart f c p) := by
  unfold cellChart
  rw [D.rawCellChart_translate]
  change SupportPair.paritySwap H (c.1+a) _=SupportPair.paritySwap H a _
  rw [add_comm,SupportPair.paritySwap_add]

theorem skeletonMap_translate (f : V → IntervalCarriers.Vertex) (a : ℤ)
    (p : Probability V) : D.skeletonMap (IntervalCarriers.translate a ∘ f) p=
      SupportPair.paritySwap H a (D.skeletonMap f p) := by
  unfold skeletonMap
  change SupportPair.paritySwap H (p.minimumCoordinate (fun v => (f v).1+a))
    (D.a (Probability.parameter (fun v => if p.minimumCoordinate (fun w => (f w).1+a)<(f v).1+a then 1 else 0) p))=_
  rw [Probability.minimumCoordinate_add]
  simp only [add_lt_add_iff_right]
  rw [add_comm,SupportPair.paritySwap_add]

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





theorem IsFanTriangle.translated {m : ℕ} {c : Vertex} {t : Finset Vertex}
    (ht : IsFanTriangle m c t) (a : ℤ) : IsFanTriangle m (translate a c) (t.image (translate a)) := by
  rcases ht with rfl | ⟨n,hn,rfl⟩
  · exact Or.inl (translate_upperTriangle m c a)
  · exact Or.inr ⟨n,hn,translate_lowerTriangle m c n a⟩

theorem RawSupported.push_translate {K : ℕ} {A B : ℤ} (a : ℤ)
    {p : Probability (CarrierVertex K A B)} {s : Finset Vertex} (hp : RawSupported p s) :
    RawSupported (Probability.push (vertexTranslation a) p) (s.image (translate a)) := by
  intro w hw
  obtain ⟨v,hv,hpv⟩ := (Probability.push_pos_iff (vertexTranslation a) p w).mp hw
  rw [←hv]
  exact Finset.mem_image.mpr ⟨v.1,hp v hpv,rfl⟩

theorem SkeletonSupported.push_translate {m K : ℕ} {A B : ℤ} (a : ℤ)
    {p : Probability (CarrierVertex K A B)} (hp : SkeletonSupported (m := m) p) :
    SkeletonSupported (m := m) (Probability.push (vertexTranslation a) p) := by
  rcases hp with ⟨v,hv,hp⟩ | ⟨u,hu,v,hv,he,hp⟩
  · refine Or.inl ⟨translate a v,(translate_mem_carrierVertices a v).mpr hv,?_⟩
    simpa only [Finset.image_singleton] using hp.push_translate a
  · have he' : (graph m).Adj (translate a u) (translate a v) :=
      (carrierTranslation m K A B a).map_rel_iff.mpr
        (show (carrierGraph m K A B).Adj ⟨u,hu⟩ ⟨v,hv⟩ from he)
    refine Or.inr ⟨translate a u,(translate_mem_carrierVertices a u).mpr hu,
      translate a v,(translate_mem_carrierVertices a v).mpr hv,he',?_⟩
    simpa only [Finset.image_insert,Finset.image_singleton] using hp.push_translate a

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

theorem solution {K : ℕ} {A B : ℤ} (a : ℤ)
    (p : Realization (2*D.power+1) K A B) :
    D.carrierProjection K (A+a) (B+a) (realizationTranslation a p)=
      SupportPair.paritySwap H a (D.carrierProjection K A B p) := by
  have hf : (Subtype.val : CarrierVertex K (A+a) (B+a) → Vertex) ∘ vertexTranslation a=
      translate a ∘ (Subtype.val : CarrierVertex K A B → Vertex) := rfl
  rcases realization_skeleton_or_cell p with hsk | ⟨c,hc,t,ht,hpt⟩
  · have hsk' : SkeletonSupported (m := 2*D.power+1) (realizationTranslation a p).1 := hsk.push_translate a
    rw [carrierProjection,(D.projectionCharts K (A+a) (B+a)).eval_eq_skeleton (by omega) _ hsk']
    rw [carrierProjection,(D.projectionCharts K A B).eval_eq_skeleton (by omega) _ hsk]
    change D.skeletonMap Subtype.val (Probability.push (vertexTranslation a) p.1)=
      SupportPair.paritySwap H a (D.skeletonMap Subtype.val p.1)
    rw [D.skeletonMap_push,hf,D.skeletonMap_translate]
  · have hc' := (translate_mem_carrierCells a c).mpr hc
    have ht' := ht.translated a
    have hpt' : RawSupported (realizationTranslation a p).1 (t.image (translate a)) := hpt.push_translate a
    rw [carrierProjection,(D.projectionCharts K (A+a) (B+a)).eval_eq_cell (by omega) _ (translate a c) hc' _ ht' hpt']
    rw [carrierProjection,(D.projectionCharts K A B).eval_eq_cell (by omega) _ c hc t ht hpt]
    change D.cellChart Subtype.val (translate a c) (Probability.push (vertexTranslation a) p.1)=
      SupportPair.paritySwap H a (D.cellChart Subtype.val c p.1)
    rw [D.cellChart_push,hf,D.cellChart_translate]
