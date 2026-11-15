-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.image_true_sdiff_image_false
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:01.243227+00:00
-- url     : https://prove2.me/submissions/4cc4afbb-bb33-499a-baf4-d33b747cf8e1

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledEdge_false_ne_true_of_mem_complement
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_image_forget_doubledEdge

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Duplicating the variables outside one bundle edge

The squared remainder in the bundle counting argument identifies the
variables on a selected edge `g₀` and takes two independent copies of every
variable outside `g₀`.  This file realizes that operation as a finite
hypergraph bundle.

An occurrence vertex in the doubled bundle is either a shared vertex of
`g₀`, or an outside vertex together with a Boolean copy label.  Every
remaining occurrence edge is lifted once into each copy.  The lift is
injective, preserves edge cardinality and projected base edges, and
therefore produces another valid bundle over the same base hypergraph.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}































/-- An edge wholly contained in the shared edge is unchanged by its copy
label.  This is the precise collision which prevents treating doubled
edges as a multiset-free bundle without an extra hypothesis. -/
theorem doubledEdge_copy_independent_of_subset
    (g₀ : Finset K) {g : Finset K}
    (hg : g ⊆ g₀) (copy copy' : Bool) :
    doubledEdge g₀ copy g =
      doubledEdge g₀ copy' g := by
  unfold doubledEdge
  apply Finset.image_congr
  intro v hv
  simp [doubledVertexLift, hg hv]



/-- The two labelled copies coincide exactly when the old edge has no
outside vertex. -/
theorem doubledEdge_false_eq_true_iff_subset
    (g₀ : Finset K) (g : Finset K) :
    doubledEdge g₀ false g =
        doubledEdge g₀ true g ↔
      g ⊆ g₀ := by
  constructor
  · intro hedges v hvg
    by_contra hvoutside
    exact
      doubledEdge_false_ne_true_of_mem_complement
        g₀ hvg hvoutside hedges
  · intro hg
    exact doubledEdge_copy_independent_of_subset
      g₀ hg false true

























































end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
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
/-- Removing the first-copy image from the second-copy image leaves
exactly those old edges which meet the complement of the shared edge. -/
theorem solution
    (g₀ : Finset K) (s : Finset (Finset K)) :
    s.image (doubledEdge g₀ true) \
        s.image (doubledEdge g₀ false) =
      (s.filter fun g => ¬ g ⊆ g₀).image
        (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    have hdtrue :
        d ∈ s.image (doubledEdge g₀ true) :=
      (Finset.mem_sdiff.mp hd).1
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hdtrue
    subst d
    apply Finset.mem_image.mpr
    refine ⟨g, Finset.mem_filter.mpr ⟨hg, ?_⟩, rfl⟩
    intro hgsub
    apply (Finset.mem_sdiff.mp hd).2
    apply Finset.mem_image.mpr
    refine ⟨g, hg, ?_⟩
    exact
      (doubledEdge_copy_independent_of_subset
        g₀ hgsub false true)
  · intro hd
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hd
    subst d
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr
      ⟨g, (Finset.mem_filter.mp hg).1, rfl⟩, ?_⟩
    intro hfalse
    obtain ⟨h, hh, hhg⟩ :=
      Finset.mem_image.mp hfalse
    have hgh : h = g := by
      have himage :=
        congrArg
          (Finset.image (doubledVertexForget g₀)) hhg
      simpa using himage
    subst h
    exact (Finset.mem_filter.mp hg).2
      ((doubledEdge_false_eq_true_iff_subset
        g₀ g).1 hhg)
