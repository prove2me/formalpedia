-- Prove2me | Definitions.Def_AT260939824_CarrierHeightCut
-- name    : AT260939824_CarrierHeightCut
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:59:15.004081+00:00
-- url     : https://prove2.me/theorems/7c6e059e-2ed7-4686-baea-deb95dd5c351
-- title:
--   Restriction of carrier faces to a lower height
-- statement:
--   For integer interval $[A,B]$, a vertex already below height $K$ remains in the height-$K$ carrier when viewed inside height $K+1$. Vertices can also be lowered by replacing their height with its minimum with $K$. For $m\ge1$, any permitted height-$K+1$ face whose vertices all lie below $K$ is a permitted height-$K$ face.
--
--   These facts justify restricting probability support after a top-layer deformation.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierHeightCut.lean, selected declaration lines 5-7, 9-11, 13-20, 22-86; SHA-256 1fbd02bdf6ca9f20a055912eabb6c60669a6eb35c6cd5d1db96ce24fabf9b8ae. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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

namespace AbelianTargets.IntervalCarriers

theorem mem_carrierVertices_lower {K : ℕ} {A B : ℤ} {v : Vertex}
    (hv : v ∈ carrierVertices (K+1) A B) (hheight : v.2 ≤ K) : v ∈ carrierVertices K A B :=
  mem_carrierVertices.mpr ⟨(mem_carrierVertices.mp hv).1,(mem_carrierVertices.mp hv).2.1,hheight⟩

theorem lower_vertex_mem {K : ℕ} {A B : ℤ} (v : Vertex)
    (hv : v ∈ carrierVertices (K+1) A B) : (v.1,min v.2 K) ∈ carrierVertices K A B :=
  mem_carrierVertices.mpr ⟨(mem_carrierVertices.mp hv).1,(mem_carrierVertices.mp hv).2.1,min_le_right _ _⟩

theorem subset_pair_drop_left {V : Type*} [DecidableEq V] {s : Finset V} {x y : V}
    (hs : s ⊆ {x,y}) (hx : x ∉ s) : s ⊆ {y} := by
  intro v hv
  have h := hs hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at h ⊢
  rcases h with h | h
  · exact (hx (by simpa only [h] using hv)).elim
  · exact h

theorem CarrierFace.lower_of_height {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) {s : Finset Vertex}
    (hs : CarrierFace m (K+1) A B s) (hheight : ∀ v ∈ s, v.2 ≤ K) : CarrierFace m K A B s := by
  rcases hs with ⟨x,hx,hs⟩ | ⟨x,hx,y,hy,he,hs⟩ | ⟨t,ht,hs⟩
  · by_cases hxl : x.2 ≤ K
    · exact Or.inl ⟨x,mem_carrierVertices_lower hx hxl,hs⟩
    · refine Or.inl ⟨(x.1,min x.2 K),lower_vertex_mem x hx,?_⟩
      intro v hv
      have he := Finset.mem_singleton.mp (hs hv)
      exact (hxl (by simpa only [he] using hheight v hv)).elim
  · by_cases hxl : x.2 ≤ K
    · by_cases hyl : y.2 ≤ K
      · exact Or.inr (Or.inl ⟨x,mem_carrierVertices_lower hx hxl,y,mem_carrierVertices_lower hy hyl,he,hs⟩)
      · have hyn : y ∉ s := fun h => hyl (hheight y h)
        exact Or.inl ⟨x,mem_carrierVertices_lower hx hxl,
          subset_pair_drop_left (by simpa only [Finset.pair_comm] using hs) hyn⟩
    · have hxn : x ∉ s := fun h => hxl (hheight x h)
      have hs' := subset_pair_drop_left hs hxn
      by_cases hyl : y.2 ≤ K
      · exact Or.inl ⟨y,mem_carrierVertices_lower hy hyl,hs'⟩
      · refine Or.inl ⟨(x.1,min x.2 K),lower_vertex_mem x hx,?_⟩
        intro v hv
        have he := Finset.mem_singleton.mp (hs' hv)
        exact (hyl (by simpa only [he] using hheight v hv)).elim
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨hcv,hcj,hcr⟩ := Finset.mem_filter.mp hc
    by_cases hcl : c.2 < K
    · have hc' : c ∈ carrierCells m K A B :=
        Finset.mem_filter.mpr ⟨mem_carrierVertices_lower hcv (by omega),hcl,hcr⟩
      rcases Finset.mem_insert.mp ht with ht | ht
      · subst t
        exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_upper hc',hs⟩)
      · obtain ⟨n,hn,ht⟩ := Finset.mem_image.mp ht
        subst t
        exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_lower hc' (Finset.mem_range.mp hn),hs⟩)
    · have hcK : c.2 = K := by omega
      rcases Finset.mem_insert.mp ht with ht | ht
      · subst t
        have hvl : lowerVertex m c.1 c.2 m ∈ carrierVertices K A B :=
          mem_carrierVertices_lower (lowerVertex_mem_of_cell hc le_rfl) (by dsimp [lowerVertex]; omega)
        refine Or.inl ⟨_,hvl,?_⟩
        intro v hv
        have hv' := hs hv
        simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hv'
        rcases hv' with h | h | h
        · have hh := hheight v hv
          rw [h] at hh; dsimp [upperLeft] at hh; omega
        · exact Finset.mem_singleton.mpr h
        · have hh := hheight v hv
          rw [h] at hh; dsimp [upperRight] at hh; omega
      · obtain ⟨n,hn,ht⟩ := Finset.mem_image.mp ht
        subst t
        have hnm : n < m := Finset.mem_range.mp hn
        have hvn : lowerVertex m c.1 c.2 n ∈ carrierVertices K A B :=
          mem_carrierVertices_lower (lowerVertex_mem_of_cell hc (by omega)) (by dsimp [lowerVertex]; omega)
        have hvn' : lowerVertex m c.1 c.2 (n+1) ∈ carrierVertices K A B :=
          mem_carrierVertices_lower (lowerVertex_mem_of_cell hc (by omega)) (by dsimp [lowerVertex]; omega)
        refine Or.inr (Or.inl ⟨_,hvn,_,hvn',horizontal_adj hm (lowerVertex_step _ _ _ _),?_⟩)
        intro v hv
        have hv' := hs hv
        simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hv'
        rcases hv' with h | h | h
        · have hh := hheight v hv
          rw [h] at hh; dsimp [upperLeft] at hh; omega
        · simp [h]
        · simp [h]

end AbelianTargets.IntervalCarriers


