-- Prove2me | Definitions.Def_AT260939824_CarrierNesting
-- name    : AT260939824_CarrierNesting
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:00:36.189096+00:00
-- url     : https://prove2.me/theorems/f2a37f8a-2969-4e68-87d1-50da7bcd7a3e
-- title:
--   Height inclusions and restrictions for carriers
-- statement:
--   For fixed base $m$ and integer interval $[A,B]$, increasing the allowed height from $K$ to $T\ge K$ preserves vertices, relation cells, and permitted faces. Pushforward along the vertex inclusion gives an isometric inclusion of probability realizations. When positive probability support is already below a lower height, the corresponding restriction recovers a point of the smaller carrier.
--
--   This interface keeps all stages of a downward deformation inside one initial carrier.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierNesting.lean, selected declaration lines 11-33, 35-41, 43-52, 54-58, 60-61, 63-85, 87-96; SHA-256 0e9bda2af219636fc9ef997258755eb658fc7d23de125b2d64570a6176422ed0. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightCut
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushGeometry
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
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

namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

theorem carrierVertices_height_mono {K T : ℕ} {A B : ℤ} (hKT : K ≤ T) :
    carrierVertices K A B ⊆ carrierVertices T A B := by
  intro v hv
  obtain ⟨hA,hB,hK⟩ := mem_carrierVertices.mp hv
  exact mem_carrierVertices.mpr ⟨hA,hB,hK.trans hKT⟩
theorem carrierCells_height_mono {m K T : ℕ} {A B : ℤ} (hKT : K ≤ T) :
    carrierCells m K A B ⊆ carrierCells m T A B := by
  intro c hc
  obtain ⟨hv,hj,hr⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨carrierVertices_height_mono hKT hv,hj.trans_le hKT,hr⟩
theorem CarrierFace.height_mono {m K T : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : CarrierFace m K A B s) (hKT : K ≤ T) : CarrierFace m T A B s := by
  rcases hs with ⟨v,hv,hs⟩ | ⟨u,hu,v,hv,he,hs⟩ | ⟨t,ht,hs⟩
  · exact Or.inl ⟨v,carrierVertices_height_mono hKT hv,hs⟩
  · exact Or.inr (Or.inl ⟨u,carrierVertices_height_mono hKT hu,v,carrierVertices_height_mono hKT hv,he,hs⟩)
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · subst t
      exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_upper (carrierCells_height_mono hKT hc),hs⟩)
    · obtain ⟨n,hn,ht⟩ := Finset.mem_image.mp ht
      subst t
      exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_lower (carrierCells_height_mono hKT hc)
        (Finset.mem_range.mp hn),hs⟩)

def vertexInclude {K T : ℕ} {A B : ℤ} (hKT : K ≤ T) (v : CarrierVertex K A B) : CarrierVertex T A B :=
  ⟨v.1,carrierVertices_height_mono hKT v.2⟩
theorem vertexInclude_injective {K T : ℕ} {A B : ℤ} (hKT : K ≤ T) :
    Function.Injective (vertexInclude (A := A) (B := B) hKT) := by
  intro u v h
  have hh : u.1 = v.1 := congrArg (fun w : CarrierVertex T A B => w.1) h
  exact Subtype.ext hh

def carrierInclude {m K T : ℕ} {A B : ℤ} (hKT : K ≤ T) (p : Realization m K A B) : Realization m T A B := by
  refine ⟨Probability.push (vertexInclude hKT) p.1,?_⟩
  obtain ⟨s,hs,hp⟩ := p.2
  refine ⟨s.image (vertexInclude hKT),?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    exact ((mem_simplexFaces s).mp hs).height_mono hKT
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (vertexInclude hKT) p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,hp v hvp,hv⟩

theorem isometry_include {m K T : ℕ} {A B : ℤ} (hKT : K ≤ T) :
    Isometry (carrierInclude (m := m) (A := A) (B := B) hKT) := by
  apply Isometry.of_dist_eq
  intro p q
  exact (Probability.isometry_push (vertexInclude hKT) (vertexInclude_injective hKT)).dist_eq p.1 q.1

def vertexLower {K : ℕ} {A B : ℤ} (v : CarrierVertex (K+1) A B) : CarrierVertex K A B :=
  ⟨(v.1.1,min v.1.2 K),lower_vertex_mem v.1 v.2⟩

def restrictHeight {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B)
    (hp : ∀ v, 0 < p.1.mass v → v.1.2 ≤ K) : Realization m K A B := by
  refine ⟨Probability.push vertexLower p.1,?_⟩
  let s := p.1.positiveSupport
  have hs : s ∈ simplexFaces m (K+1) A B := positiveSupport_mem p
  have hface := ((mem_simplexFaces s).mp hs).lower_of_height hm (by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hp w ((Probability.mem_positiveSupport p.1 w).mp hw))
  refine ⟨s.image vertexLower,?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    have he : s.image (fun v => (vertexLower v).1) = s.image Subtype.val := by
      apply Finset.image_congr
      intro v hv
      have hh := hp v ((Probability.mem_positiveSupport p.1 v).mp hv)
      simp only [vertexLower,min_eq_left hh,Prod.eta]
    change CarrierFace m K A B (s.image (fun v => (vertexLower v).1))
    rw [he]
    exact hface
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff vertexLower p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,(Probability.mem_positiveSupport p.1 v).mpr hvp,hv⟩

theorem include_restrictHeight {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B)
    (hp : ∀ v, 0 < p.1.mass v → v.1.2 ≤ K) :
    carrierInclude (by omega : K ≤ K+1) (restrictHeight hm p hp) = p := by
  apply Subtype.ext
  change Probability.push (vertexInclude (by omega : K ≤ K+1)) (Probability.push vertexLower p.1) = p.1
  rw [Probability.push_comp]
  apply Probability.push_eq_self
  intro v hv
  apply Subtype.ext
  simp only [Function.comp_def,vertexInclude,vertexLower,min_eq_left (hp v hv),Prod.eta]





end
end AbelianTargets.IntervalCarriers


