-- Prove2me | Definitions.Def_AT260939824_CarrierProjectionGluing
-- name    : AT260939824_CarrierProjectionGluing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:21:55.538852+00:00
-- url     : https://prove2.me/theorems/4d6d3ee5-fa6c-4a6d-a765-52c36f348581
-- title:
--   Compatible skeleton and cell charts on an interval carrier
-- statement:
--   Consider the finite triangulated interval carrier with base $m$, height $K$, and horizontal interval $[A,B]$. A probability distribution is raw-supported on a vertex set when every vertex with positive mass belongs to that set. Skeleton support means support in a single vertex or a graph edge.
--
--   Projection-chart data into a topological space $Z$ consist of a skeleton formula continuous on each vertex and edge face, together with continuous whole-cell charts agreeing with that formula on their skeleton portions. A simplex face uses a containing cell chart when one exists and otherwise uses the skeleton formula. For $m\ge1$, the compatibility lemmas produce a well-defined evaluation on the carrier realization, equal to the skeleton formula on every skeleton-supported distribution.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/CarrierProjectionGluing.lean, selected declaration lines 12-13, 15-17, 19-20, 22-24, 26-27, 29-36, 38-46, 51-53, 55-67, 69-80, 82-98, 100-124, 126-130, 132-133, 138-147; SHA-256 6292cc79a9be79a98223cbfc53b15537731222a3d3d6f329b428789046a0d5aa. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleChartIntersections
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
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

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Global carrier projections assembled from polygon and skeleton charts. -/
namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

def RawSupported {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B)) (s : Finset Vertex) : Prop :=
  ∀ v,0<p.mass v→v.1∈s

def SkeletonSupported {m K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex K A B)) : Prop :=
  (∃ v∈carrierVertices K A B,RawSupported p {v}) ∨
    ∃ u∈carrierVertices K A B,∃ v∈carrierVertices K A B,(graph m).Adj u v ∧ RawSupported p {u,v}

def FaceHasCell {m K : ℕ} {A B : ℤ} (s : Finset (CarrierVertex K A B)) : Prop :=
  ∃ c∈carrierCells m K A B,∃ t,IsFanTriangle m c t ∧ s.image Subtype.val⊆t

theorem rawSupported_of_face {K : ℕ} {A B : ℤ} {p : Probability (CarrierVertex K A B)}
    {s : Finset (CarrierVertex K A B)} (hp : p.SupportedOn (s : Set _)) :
    RawSupported p (s.image Subtype.val) := fun v hv => Finset.mem_image.mpr ⟨v,hp v hv,rfl⟩

theorem RawSupported.mono {K : ℕ} {A B : ℤ} {p : Probability (CarrierVertex K A B)}
    {s t : Finset Vertex} (hp : RawSupported p s) (h : s⊆t) : RawSupported p t := fun v hv => h (hp v hv)

theorem skeletonSupported_without_cell {m K : ℕ} {A B : ℤ}
    {s : Finset (CarrierVertex K A B)} (hs : s∈simplexFaces m K A B) (hn : ¬FaceHasCell (m := m) s)
    {p : Probability (CarrierVertex K A B)} (hp : p.SupportedOn (s : Set _)) : SkeletonSupported (m := m) p := by
  rcases (mem_simplexFaces s).mp hs with ⟨v,hv,hsub⟩ | ⟨u,hu,v,hv,he,hsub⟩ | ⟨t,ht,hsub⟩
  · exact Or.inl ⟨v,hv,(rawSupported_of_face hp).mono hsub⟩
  · exact Or.inr ⟨u,hu,v,hv,he,(rawSupported_of_face hp).mono hsub⟩
  · obtain ⟨c,hc,hct⟩ := fanTriangle_of_carrierTriangle ht
    exact False.elim (hn ⟨c,hc,t,hct,hsub⟩)

structure CarrierProjectionCharts (m K : ℕ) (A B : ℤ) (Z : Type*) [TopologicalSpace Z] where
  skeleton : Probability (CarrierVertex K A B) → Z
  continuous_vertex : ∀ v∈carrierVertices K A B,ContinuousOn skeleton {p | RawSupported p {v}}
  continuous_edge : ∀ u∈carrierVertices K A B,∀ v∈carrierVertices K A B,(graph m).Adj u v→
    ContinuousOn skeleton {p | RawSupported p {u,v}}
  cell : Vertex → Probability (CarrierVertex K A B) → Z
  continuous_cell : ∀ c∈carrierCells m K A B,Continuous (cell c)
  cell_skeleton : ∀ c∈carrierCells m K A B,∀ t,IsFanTriangle m c t→
    ∀ p,RawSupported p t→SkeletonSupported (m := m) p→cell c p=skeleton p

namespace CarrierProjectionCharts
variable {m K : ℕ} {A B : ℤ} {Z : Type*} [TopologicalSpace Z]

def faceValue (D : CarrierProjectionCharts m K A B Z) (s : Finset (CarrierVertex K A B))
    (p : Probability (CarrierVertex K A B)) : Z :=
  if h : FaceHasCell (m := m) s then D.cell h.choose p else D.skeleton p

theorem continuous_faceValue (D : CarrierProjectionCharts m K A B Z)
    (s : Finset (CarrierVertex K A B)) (hs : s∈simplexFaces m K A B) :
    Continuous (fun p : ProbabilityFace s => D.faceValue s p.1) := by
  by_cases h : FaceHasCell (m := m) s
  · simpa only [faceValue,dif_pos h] using
      (D.continuous_cell h.choose h.choose_spec.1).comp continuous_subtype_val
  · have hc : ContinuousOn D.skeleton {p | p.SupportedOn (s : Set _)} := by
      rcases (mem_simplexFaces s).mp hs with ⟨v,hv,hsub⟩ | ⟨u,hu,v,hv,he,hsub⟩ | ⟨t,ht,hsub⟩
      · exact (D.continuous_vertex v hv).mono (fun p hp => (rawSupported_of_face hp).mono hsub)
      · exact (D.continuous_edge u hu v hv he).mono (fun p hp => (rawSupported_of_face hp).mono hsub)
      · obtain ⟨c,hc,hct⟩ := fanTriangle_of_carrierTriangle ht
        exact False.elim (h ⟨c,hc,t,hct,hsub⟩)
    simpa only [faceValue,dif_neg h] using continuousOn_iff_continuous_restrict.mp hc

 theorem raw_positiveSupport_nonempty {K : ℕ} {A B : ℤ}
    (p : Probability (CarrierVertex K A B)) : (p.positiveSupport.image Subtype.val).Nonempty := by
  have hp : p.positiveSupport.Nonempty := by
    by_contra hn
    have hz : ∀ v,p.mass v=0 := by
      intro v
      have hv : ¬0<p.mass v := fun h => hn ⟨v,(Probability.mem_positiveSupport p v).mpr h⟩
      exact le_antisymm (le_of_not_gt hv) (p.nonneg v)
    have he := p.sum_one
    simp only [hz,Finset.sum_const_zero] at he
    norm_num at he
  exact hp.image _

 theorem shared_cell_skeleton (hm : 1≤m) {p : Probability (CarrierVertex K A B)}
    {c d : Vertex} {s t : Finset Vertex} (hs : IsFanTriangle m c s) (ht : IsFanTriangle m d t)
    (hcd : c≠d) (hp : RawSupported p s) (hq : RawSupported p t) : SkeletonSupported (m := m) p := by
  let u := p.positiveSupport.image Subtype.val
  have hus : u⊆s := by
    intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hp w ((Probability.mem_positiveSupport p w).mp hw)
  have hut : u⊆t := by
    intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hq w ((Probability.mem_positiveSupport p w).mp hw)
  have huv : u⊆carrierVertices K A B := by
    intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact w.2
  have hpu : RawSupported p u := rawSupported_of_face (Probability.supportedOn_positiveSupport p)
  rcases different_fan_origins_shared_face hm hs ht hcd hus hut (raw_positiveSupport_nonempty p) huv with
    ⟨v,hv,hsub⟩ | ⟨v,hv,w,hw,he,hsub⟩
  · exact Or.inl ⟨v,hv,hpu.mono hsub⟩
  · exact Or.inr ⟨v,hv,w,hw,he,hpu.mono hsub⟩

theorem faceValue_agree (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m)
    (s : Finset (CarrierVertex K A B)) (hs : s∈simplexFaces m K A B)
    (t : Finset (CarrierVertex K A B)) (ht : t∈simplexFaces m K A B)
    (p : Probability (CarrierVertex K A B)) (hp : p.SupportedOn (s : Set _))
    (hq : p.SupportedOn (t : Set _)) : D.faceValue s p=D.faceValue t p := by
  by_cases hc : FaceHasCell (m := m) s <;> by_cases hd : FaceHasCell (m := m) t
  · simp only [faceValue,dif_pos hc,dif_pos hd]
    obtain ⟨a,ha,hpa⟩ := hc.choose_spec.2
    obtain ⟨b,hb,hpb⟩ := hd.choose_spec.2
    have hps := (rawSupported_of_face hp).mono hpa
    have hpt := (rawSupported_of_face hq).mono hpb
    by_cases he : hc.choose=hd.choose
    · rw [he]
    · have hsk := shared_cell_skeleton hm ha hb he hps hpt
      exact (D.cell_skeleton _ hc.choose_spec.1 _ ha p hps hsk).trans
        (D.cell_skeleton _ hd.choose_spec.1 _ hb p hpt hsk).symm
  · simp only [faceValue,dif_pos hc,dif_neg hd]
    obtain ⟨a,ha,hpa⟩ := hc.choose_spec.2
    exact D.cell_skeleton _ hc.choose_spec.1 _ ha p ((rawSupported_of_face hp).mono hpa)
      (skeletonSupported_without_cell ht hd hq)
  · simp only [faceValue,dif_neg hc,dif_pos hd]
    obtain ⟨b,hb,hpb⟩ := hd.choose_spec.2
    exact (D.cell_skeleton _ hd.choose_spec.1 _ hb p ((rawSupported_of_face hq).mono hpb)
      (skeletonSupported_without_cell hs hc hp)).symm
  · simp only [faceValue,dif_neg hc,dif_neg hd]

def simplicialData (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m) :
    SimplicialChartData (simplexFaces m K A B) Z where
  chart s hs p := D.faceValue s p.1
  continuous_chart := D.continuous_faceValue
  agree s hs t ht p hp hq := D.faceValue_agree hm s hs t ht p hp hq

def eval (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m) (p : Realization m K A B) : Z :=
  (D.simplicialData hm).eval p



theorem eval_eq_skeleton (D : CarrierProjectionCharts m K A B Z) (hm : 1≤m)
    (p : Realization m K A B) (hsk : SkeletonSupported (m := m) p.1) : D.eval hm p=D.skeleton p.1 := by
  obtain ⟨s,hs,hp⟩ := p.2
  rw [eval,(D.simplicialData hm).eval_eq_chart p s hs hp]
  change D.faceValue s p.1=D.skeleton p.1
  by_cases hc : FaceHasCell (m := m) s
  · rw [faceValue,dif_pos hc]
    obtain ⟨a,ha,hpa⟩ := hc.choose_spec.2
    exact D.cell_skeleton _ hc.choose_spec.1 _ ha p.1 ((rawSupported_of_face hp).mono hpa) hsk
  · simp only [faceValue,dif_neg hc]



end CarrierProjectionCharts
end
end AbelianTargets.IntervalCarriers


