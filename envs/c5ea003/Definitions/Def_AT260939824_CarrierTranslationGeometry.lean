-- Prove2me | Definitions.Def_AT260939824_CarrierTranslationGeometry
-- name    : AT260939824_CarrierTranslationGeometry
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:11:09.306984+00:00
-- url     : https://prove2.me/theorems/934bb6ea-7936-4c4a-9ac7-3cd88db51ea7
-- title:
--   Horizontal translation of carrier faces and masses
-- statement:
--   With base $m$, height $K$, and integer interval $[A,B]$, translating a raw vertex $(r,h)$ by $a$ gives $(r+a,h)$. This preserves relation cells, lower and upper triangles, and all permitted faces after translating the interval. Pushforward defines an isometric map on the probability realization.
--
--   These formulas supply the concrete geometric translation map whose inverse and equivariance properties are used elsewhere.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierTranslationGeometry.lean, selected declaration lines 11-14, 16-18, 20-22, 24-33, 35-46, 48-49, 51-56, 58-70, 72-76; SHA-256 344c9b4238c8ef801221724c4cb27e4e61fe8004c0f8d2be939b48900f99f1d0. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
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

/-! Literal horizontal translation is an isometry of barycentric carriers. -/
namespace AbelianTargets.IntervalCarriers
noncomputable section
attribute [local instance] Classical.propDecidable

theorem translate_mem_carrierCells {m K : ℕ} {A B : ℤ} (a : ℤ) (c : Vertex) :
    translate a c ∈ carrierCells m K (A+a) (B+a) ↔ c ∈ carrierCells m K A B := by
  simp only [carrierCells,Finset.mem_filter,mem_carrierVertices,translate]
  omega

theorem translate_lowerTriangle (m : ℕ) (c : Vertex) (n : ℕ) (a : ℤ) :
    (lowerTriangle m c n).image (translate a)=lowerTriangle m (translate a c) n := by
  simp [lowerTriangle,translate,upperLeft,lowerVertex,add_assoc,add_comm,add_left_comm]

theorem translate_upperTriangle (m : ℕ) (c : Vertex) (a : ℤ) :
    (upperTriangle m c).image (translate a)=upperTriangle m (translate a c) := by
  simp [upperTriangle,translate,upperLeft,upperRight,lowerVertex,add_assoc,add_comm,add_left_comm]

theorem translate_carrierTriangle {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : s ∈ carrierTriangles m K A B) (a : ℤ) :
    s.image (translate a) ∈ carrierTriangles m K (A+a) (B+a) := by
  obtain ⟨c,hc,hs⟩ := Finset.mem_biUnion.mp hs
  have hc' := (translate_mem_carrierCells a c).mpr hc
  rcases Finset.mem_insert.mp hs with he | he
  · subst s; rw [translate_upperTriangle]; exact mem_carrierTriangles_upper hc'
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp he
    rw [translate_lowerTriangle]
    exact mem_carrierTriangles_lower hc' (Finset.mem_range.mp hn)

theorem CarrierFace.translated {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : CarrierFace m K A B s) (a : ℤ) :
    CarrierFace m K (A+a) (B+a) (s.image (translate a)) := by
  rcases hs with ⟨v,hv,hs⟩ | ⟨u,hu,v,hv,he,hs⟩ | ⟨t,ht,hs⟩
  · exact Or.inl ⟨translate a v,(translate_mem_carrierVertices a v).mpr hv,
      by simpa only [Finset.image_singleton] using Finset.image_subset_image hs⟩
  · have he' : (graph m).Adj (translate a u) (translate a v) :=
      (carrierTranslation m K A B a).map_rel_iff.mpr (show (carrierGraph m K A B).Adj ⟨u,hu⟩ ⟨v,hv⟩ from he)
    exact Or.inr (Or.inl ⟨translate a u,(translate_mem_carrierVertices a u).mpr hu,
      translate a v,(translate_mem_carrierVertices a v).mpr hv,he',
      by simpa only [Finset.image_insert,Finset.image_singleton] using Finset.image_subset_image hs⟩)
  · exact Or.inr (Or.inr ⟨t.image (translate a),translate_carrierTriangle ht a,Finset.image_subset_image hs⟩)

def vertexTranslation {K : ℕ} {A B : ℤ} (a : ℤ) (v : CarrierVertex K A B) : CarrierVertex K (A+a) (B+a) :=
  ⟨translate a v.1,(translate_mem_carrierVertices a v.1).mpr v.2⟩

theorem vertexTranslation_injective {K : ℕ} {A B : ℤ} (a : ℤ) :
    Function.Injective (vertexTranslation (K := K) (A := A) (B := B) a) := by
  intro u v h
  apply Subtype.ext
  have he := congrArg (fun w : CarrierVertex K (A+a) (B+a) => translate (-a) w.1) h
  simpa [vertexTranslation,translate] using he

def realizationTranslation {m K : ℕ} {A B : ℤ} (a : ℤ) (p : Realization m K A B) :
    Realization m K (A+a) (B+a) := by
  refine ⟨Probability.push (vertexTranslation a) p.1,?_⟩
  obtain ⟨s,hs,hp⟩ := p.2
  refine ⟨s.image (vertexTranslation a),?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    rw [Finset.image_image]
    change CarrierFace m K (A+a) (B+a) (s.image (translate a ∘ Subtype.val))
    rw [←Finset.image_image]
    exact ((mem_simplexFaces s).mp hs).translated a
  · intro w hw
    obtain ⟨v,hv,hvp⟩ := (Probability.push_pos_iff (vertexTranslation a) p.1 w).mp hw
    exact Finset.mem_image.mpr ⟨v,hp v hvp,hv⟩

theorem realizationTranslation_isometry {m K : ℕ} {A B : ℤ} (a : ℤ) :
    Isometry (realizationTranslation (m := m) (K := K) (A := A) (B := B) a) := by
  apply Isometry.of_dist_eq
  intro p q
  exact (Probability.isometry_push (vertexTranslation a) (vertexTranslation_injective a)).dist_eq p.1 q.1

end
end AbelianTargets.IntervalCarriers


