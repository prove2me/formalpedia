-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledEdges_eq_image_union
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:11:52.562511+00:00
-- url     : https://prove2.me/submissions/05a82811-7f68-4fa4-a471-8cf347827ddd

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Filtrations of hypergraph bundles

The generalized counting argument repeatedly discards all edges of the
current maximal rank and then duplicates the remaining bundle around one
selected maximal edge.  This file packages the elementary structural
operations used in that step.

Besides arbitrary edge filtering, we single out the lower-order part of a
bundle and the strict boundary below a fixed edge.  The final product
identity records the only collisions caused by duplication: the two
labelled copies of a strict boundary edge coincide, whereas every other
lower-order edge contributes two distinct copies.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
/-! ## Edge-filtered subbundles -/
/-! ## The lower-order and strict-boundary filtrations -/
/-! ## Main-density products -/
/-! ## The main product under duplication -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- The doubled edge family is the union of the two fixed-copy images. -/
theorem solution
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    B.doubledEdges g₀ =
      (B.edges.erase g₀).image
          (doubledEdge g₀ false) ∪
        (B.edges.erase g₀).image
          (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    cases copy
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  · intro hd
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨false, g, hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨true, g, hg, rfl⟩
