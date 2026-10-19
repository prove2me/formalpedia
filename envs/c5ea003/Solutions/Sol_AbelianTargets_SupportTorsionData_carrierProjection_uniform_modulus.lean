-- Prove2me | solution 1 for AbelianTargets.SupportTorsionData.carrierProjection_uniform_modulus
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:10:29.501585+00:00
-- url     : https://prove2.me/submissions/b88accf1-b9c5-4aaa-b9f1-262b63c5ef4f

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
import Definitions.Def_AT260939824_SimplexMetricGluing
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportRelationCharts
import Definitions.Def_AT260939824_SupportWitness
import Definitions.Def_AT260939824_TopologicalWalks
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
import Theorems.Thm_AbelianTargets_SupportTorsionData_affineChart_uniform_face_modulus
import Theorems.Thm_AbelianTargets_SupportTorsionData_faceValue_affine_representation
import Theorems.Thm_AbelianTargets_uniform_simplex_face_modulus

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.CarrierFaceBound
section
/-! Uniform simplex dimension, independent of the size of the carrier. -/

namespace AbelianTargets.IntervalCarriers

theorem carrierTriangle_card_le {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : s ∈ carrierTriangles m K A B) : s.card ≤ 3 := by
  obtain ⟨c,hc,hs⟩ := Finset.mem_biUnion.mp hs
  obtain rfl | hs := Finset.mem_insert.mp hs
  · exact Finset.card_le_three
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.card_le_three

theorem CarrierFace.card_le_three {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : CarrierFace m K A B s) : s.card ≤ 3 := by
  rcases hs with ⟨v,hv,hsv⟩ | ⟨u,hu,v,hv,he,hsv⟩ | ⟨t,ht,hst⟩
  · exact (Finset.card_le_card hsv).trans (by simp)
  · exact (Finset.card_le_card hsv).trans (Finset.card_le_two.trans (by omega))
  · exact (Finset.card_le_card hst).trans (carrierTriangle_card_le ht)

theorem simplexFaces_card_le_three {m K : ℕ} {A B : ℤ}
    {s : Finset (CarrierVertex K A B)} (hs : s ∈ simplexFaces m K A B) : s.card ≤ 3 := by
  classical
  have hcard : (s.image Subtype.val).card=s.card :=
    Finset.card_image_of_injective s Subtype.val_injective
  rw [←hcard]
  exact ((mem_simplexFaces s).mp hs).card_le_three

end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.CarrierProjectionFaceCharts
section
namespace AbelianTargets.SupportTorsionData
noncomputable section
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
open IntervalCarriers



theorem carrierProjection_eq_faceValue (K : ℕ) (A B : ℤ)
    (p : Realization (2*D.power+1) K A B) (s : Finset (CarrierVertex K A B))
    (hs : s∈simplexFaces (2*D.power+1) K A B) (hp : p.1.SupportedOn (s:Set _)) :
    D.carrierProjection K A B p=(D.projectionCharts K A B).faceValue s p.1 := by
  exact ((D.projectionCharts K A B).simplicialData (by omega)).eval_eq_chart p s hs hp

end
end AbelianTargets.SupportTorsionData

end

-- Preserved source skeleton: AbelianTargets.UniformCarrierSupportProjection
section
/-! One modulus for every finite interval-carrier projection. -/
namespace AbelianTargets.SupportTorsionData
noncomputable section
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
open IntervalCarriers

theorem carrierProjection_face_modulus :
    ∀ ε:ℝ,0<ε→∃δ:ℝ,0<δ ∧ ∀(K:ℕ)(A B:ℤ)
      (s:Finset (CarrierVertex K A B)),s∈simplexFaces (2*D.power+1) K A B→
      ∀p q:Realization (2*D.power+1) K A B,
        p.1.SupportedOn (s:Set _)→q.1.SupportedOn (s:Set _)→
        dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε := by
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := D.affineChart_uniform_face_modulus ε hε
  refine ⟨δ,hδ,?_⟩
  intro K A B s hs p q hp hq hd
  obtain ⟨r,height,theta,hrepr⟩ := D.faceValue_affine_representation K A B s hs
  rw [D.carrierProjection_eq_faceValue K A B p s hs hp,
    D.carrierProjection_eq_faceValue K A B q s hs hq,hrepr p.1 hp,hrepr q.1 hq]
  exact hbound height theta r s p.1 q.1 (simplexFaces_card_le_three hs) hp hq hd



end
end AbelianTargets.SupportTorsionData

end

/-! One modulus for every finite interval-carrier projection. -/
namespace AbelianTargets.SupportTorsionData
end AbelianTargets.SupportTorsionData
open AbelianTargets
open AbelianTargets.SupportTorsionData
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)
open IntervalCarriers

theorem solution :
    ∀ ε:ℝ,0<ε→∃δ:ℝ,0<δ ∧ ∀(K:ℕ)(A B:ℤ)
      (p q:Realization (2*D.power+1) K A B),
        dist p q<δ→dist (D.carrierProjection K A B p) (D.carrierProjection K A B q)<ε := by
  let F (i:ℕ×ℤ×ℤ) := simplexFaces (2*D.power+1) i.1 i.2.1 i.2.2
  let f (i:ℕ×ℤ×ℤ) := D.carrierProjection i.1 i.2.1 i.2.2
  have hface : ∀ε:ℝ,0<ε→∃δ:ℝ,0<δ ∧ ∀i s,s∈F i→
      ∀p q:SimplicialCarrier (F i),p.1.SupportedOn (s:Set _)→q.1.SupportedOn (s:Set _)→
        dist p q<δ→dist (f i p) (f i q)<ε := by
    intro ε hε
    obtain ⟨δ,hδ,hbound⟩ := D.carrierProjection_face_modulus ε hε
    exact ⟨δ,hδ,fun i s hs p q hp hq hd => hbound i.1 i.2.1 i.2.2 s hs p q hp hq hd⟩
  have hglobal := uniform_simplex_face_modulus F f 3
    (fun i s hs => simplexFaces_card_le_three hs) hface
  intro ε hε
  obtain ⟨δ,hδ,hbound⟩ := hglobal ε hε
  exact ⟨δ,hδ,fun K A B p q h => hbound (K,A,B) p q h⟩
