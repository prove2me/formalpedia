-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleMainProduct_duplicateOutside
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:15:39.116783+00:00
-- url     : https://prove2.me/submissions/8f5fbe5e-e830-4489-b3ff-41de3a359858

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledEdges_eq_image_union
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_image_forget_doubledEdge
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_image_true_sdiff_image_false

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





























































@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl

@[simp]
theorem duplicateOutside_projection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).projection =
      B.doubledProjection g₀ :=
  rfl





























end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section


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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Edge-filtered subbundles -/















/-! ## The lower-order and strict-boundary filtrations -/





























/-! ## Main-density products -/













/-! ## The main product under duplication -/

/-- A fixed labelled lift is injective on occurrence edges.  Forgetting
the doubled vertices is a left inverse. -/
theorem doubledEdge_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledEdge g₀ copy) := by
  intro g h hgh
  have himage :=
    congrArg
      (Finset.image (doubledVertexForget g₀)) hgh
  simpa using himage





/-- A fixed-copy image has the same projected main-density product as its
source edge family. -/
theorem prod_image_doubledEdge_main
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (copy : Bool)
    (s : Finset (Finset K))
    (p : Finset J → ℝ) :
    (∏ d ∈ s.image (doubledEdge g₀ copy),
        p (d.image (B.doubledProjection g₀))) =
      ∏ g ∈ s, p (g.image B.projection) := by
  classical
  rw [Finset.prod_image
    (doubledEdge_injective g₀ copy).injOn]
  simp





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
/-- General main-density product identity for duplication.  Edges
contained in `g₀` have only one actual doubled copy; all other remaining
edges have two. -/
theorem solution
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.duplicateOutside g₀).bundleMainProduct p =
      (∏ g ∈ (B.edges.erase g₀).filter
          (fun g => g ⊆ g₀),
        p (g.image B.projection)) *
      ∏ g ∈ (B.edges.erase g₀).filter
          (fun g => ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  let s := B.edges.erase g₀
  let first :=
    s.image (doubledEdge g₀ false)
  let second :=
    s.image (doubledEdge g₀ true)
  have hsplit :
      (∏ g ∈ s.filter (fun g => g ⊆ g₀),
          p (g.image B.projection)) *
          (∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) =
        ∏ g ∈ s, p (g.image B.projection) :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  calc
    (B.duplicateOutside g₀).bundleMainProduct p =
        ∏ d ∈ first ∪ second,
          p (d.image (B.doubledProjection g₀)) := by
      unfold bundleMainProduct first second
      simp only [duplicateOutside_edges,
        duplicateOutside_projection]
      rw [B.doubledEdges_eq_image_union g₀]
    _ = ∏ d ∈ first ∪ (second \ first),
          p (d.image (B.doubledProjection g₀)) := by
      rw [Finset.union_sdiff_self_eq_union]
    _ =
        (∏ d ∈ first,
          p (d.image (B.doubledProjection g₀))) *
        ∏ d ∈ second \ first,
          p (d.image (B.doubledProjection g₀)) := by
      exact Finset.prod_union Finset.disjoint_sdiff
    _ =
        (∏ g ∈ s, p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      unfold first second
      rw [image_true_sdiff_image_false]
      rw [B.prod_image_doubledEdge_main g₀ false]
      rw [B.prod_image_doubledEdge_main g₀ true]
    _ =
        ((∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      rw [hsplit]
    _ =
        (∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            (p (g.image B.projection)) ^ 2 := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [pow_two]
    _ = _ := rfl
