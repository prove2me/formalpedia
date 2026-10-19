-- Prove2me | Definitions.Def_AT260939824_CarrierTriangulation
-- name    : AT260939824_CarrierTriangulation
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:45:58.997501+00:00
-- url     : https://prove2.me/theorems/f0ec1401-5c48-4b92-bd89-56aaebe55bce
-- title:
--   The fan triangulation of interval relation cells
-- statement:
--   Each carrier relation polygon with base $m$ has a lower side with $m$ edges and an upper side at the next height. Its lower triangles join consecutive lower vertices to the upper-left vertex; one upper triangle completes the polygon. A permitted carrier face is a subset of a vertex, a graph edge, or one of these triangles.
--
--   This finite face system defines the simplex realization used for the controlled carrier geometry.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierTriangulation.lean, selected declaration lines 15-16, 18-19, 21-22, 24-26, 28-32, 34-41, 43-51, 53-60, 62-66, 68-71, 73-79, 81-87, 89-94, 96-108; SHA-256 2ae1f0e6a85f9abf97bb97b5950d33f677d112e47b4e99b5b42b9a4f5d2881dc. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_IntervalCarriers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Finite polygon fans in the actual interval carrier

Each presentation polygon is triangulated from its upper left vertex.
The lower fan has one triangle per lower edge and one final triangle
at the upper right corner. Every simplex vertex is a proved member of
the literal finite carrier.
-/

namespace AbelianTargets.IntervalCarriers

def upperLeft (r : ℤ) (j : ℕ) : Vertex := (r,j+1)
def upperRight (m : ℕ) (r : ℤ) (j : ℕ) : Vertex := (r+(m:ℤ)^(j+1),j+1)

def lowerTriangle (m : ℕ) (c : Vertex) (n : ℕ) : Finset Vertex :=
  {upperLeft c.1 c.2,lowerVertex m c.1 c.2 n,lowerVertex m c.1 c.2 (n+1)}

def upperTriangle (m : ℕ) (c : Vertex) : Finset Vertex :=
  {upperLeft c.1 c.2,lowerVertex m c.1 c.2 m,upperRight m c.1 c.2}

def carrierTriangles (m K : ℕ) (A B : ℤ) : Finset (Finset Vertex) :=
  (carrierCells m K A B).biUnion (fun c =>
    insert (upperTriangle m c) ((Finset.range m).image (lowerTriangle m c)))

theorem upperLeft_mem_of_cell {m K : ℕ} {A B : ℤ} {c : Vertex}
    (hc : c ∈ carrierCells m K A B) : upperLeft c.1 c.2 ∈ carrierVertices K A B := by
  obtain ⟨hv,hj,hr⟩ := Finset.mem_filter.mp hc
  obtain ⟨hA,hB,_⟩ := mem_carrierVertices.mp hv
  exact mem_carrierVertices.mpr ⟨hA,hB,by dsimp [upperLeft]; omega⟩

theorem upperRight_mem_of_cell {m K : ℕ} {A B : ℤ} {c : Vertex}
    (hc : c ∈ carrierCells m K A B) : upperRight m c.1 c.2 ∈ carrierVertices K A B := by
  obtain ⟨hv,hj,hr⟩ := Finset.mem_filter.mp hc
  obtain ⟨hA,hB,_⟩ := mem_carrierVertices.mp hv
  apply mem_carrierVertices.mpr
  dsimp [upperRight]
  have hs : 0 ≤ (m:ℤ)^(c.2+1) := pow_nonneg (by positivity) _
  exact ⟨by omega,hr,by omega⟩

theorem lowerTriangle_vertices {m K n : ℕ} {A B : ℤ} {c : Vertex}
    (hc : c ∈ carrierCells m K A B) (hn : n < m) :
    lowerTriangle m c n ⊆ carrierVertices K A B := by
  intro v hv
  simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hv
  obtain rfl | rfl | rfl := hv
  · exact upperLeft_mem_of_cell hc
  · exact lowerVertex_mem_of_cell hc (by omega)
  · exact lowerVertex_mem_of_cell hc (by omega)

theorem upperTriangle_vertices {m K : ℕ} {A B : ℤ} {c : Vertex}
    (hc : c ∈ carrierCells m K A B) : upperTriangle m c ⊆ carrierVertices K A B := by
  intro v hv
  simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hv
  obtain rfl | rfl | rfl := hv
  · exact upperLeft_mem_of_cell hc
  · exact lowerVertex_mem_of_cell hc le_rfl
  · exact upperRight_mem_of_cell hc

theorem mem_carrierTriangles_lower {m K n : ℕ} {A B : ℤ} {c : Vertex}
    (hc : c ∈ carrierCells m K A B) (hn : n < m) : lowerTriangle m c n ∈ carrierTriangles m K A B := by
  apply Finset.mem_biUnion.mpr
  refine ⟨c,hc,Finset.mem_insert.mpr (Or.inr ?_)⟩
  exact Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hn,rfl⟩

theorem mem_carrierTriangles_upper {m K : ℕ} {A B : ℤ} {c : Vertex}
    (hc : c ∈ carrierCells m K A B) : upperTriangle m c ∈ carrierTriangles m K A B := by
  apply Finset.mem_biUnion.mpr
  exact ⟨c,hc,Finset.mem_insert_self _ _⟩

theorem carrierTriangle_vertices {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : s ∈ carrierTriangles m K A B) : s ⊆ carrierVertices K A B := by
  obtain ⟨c,hc,hs⟩ := Finset.mem_biUnion.mp hs
  obtain rfl | hs := Finset.mem_insert.mp hs
  · exact upperTriangle_vertices hc
  · obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hs
    exact lowerTriangle_vertices hc (Finset.mem_range.mp hn)

/-- The downward-closed finite simplicial face family. It includes
all carrier vertices and all faces of the fan triangles. -/
def CarrierFace (m K : ℕ) (A B : ℤ) (s : Finset Vertex) : Prop :=
  (∃ v ∈ carrierVertices K A B, s ⊆ {v}) ∨
    (∃ u ∈ carrierVertices K A B, ∃ v ∈ carrierVertices K A B,
      (graph m).Adj u v ∧ s ⊆ {u,v}) ∨
    ∃ t ∈ carrierTriangles m K A B, s ⊆ t

theorem CarrierFace.downward {m K : ℕ} {A B : ℤ} {s t : Finset Vertex}
    (hs : CarrierFace m K A B s) (ht : t ⊆ s) : CarrierFace m K A B t := by
  obtain ⟨v,hv,hs⟩ | ⟨u,hu,v,hv,he,hs⟩ | ⟨u,hu,hs⟩ := hs
  · exact Or.inl ⟨v,hv,ht.trans hs⟩
  · exact Or.inr (Or.inl ⟨u,hu,v,hv,he,ht.trans hs⟩)
  · exact Or.inr (Or.inr ⟨u,hu,ht.trans hs⟩)

theorem CarrierFace.vertices {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : CarrierFace m K A B s) : s ⊆ carrierVertices K A B := by
  obtain ⟨v,hv,hs⟩ | ⟨u,hu,v,hv,he,hs⟩ | ⟨u,hu,hs⟩ := hs
  · intro x hx
    have : x = v := Finset.mem_singleton.mp (hs hx)
    simpa only [this] using hv
  · intro x hx
    have hx' := hs hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx'
    obtain rfl | rfl := hx'
    · exact hu
    · exact hv
  · exact hs.trans (carrierTriangle_vertices hu)

end AbelianTargets.IntervalCarriers


