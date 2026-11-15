-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.card_duplicateOutside_lowerOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:19:56.280217+00:00
-- url     : https://prove2.me/submissions/121666f6-55df-47ff-8f58-a6b5baadea95

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

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









/-- There are at most two doubled occurrence edges for each remaining
source edge. -/
theorem card_doubledEdges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.doubledEdges g₀).card ≤
      2 * (B.edges.erase g₀).card := by
  unfold doubledEdges
  calc
    (Finset.univ.image
        (B.doubledEdgeOfSource g₀)).card ≤
        (Finset.univ :
          Finset (B.DoubledEdgeSource g₀)).card :=
      Finset.card_image_le
    _ = 2 * (B.edges.erase g₀).card := by
      simp [DoubledEdgeSource]





















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











/-- Edge filtering cannot increase the number of occurrence edges. -/
theorem card_filterEdges_edges_le
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges.card ≤ B.edges.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)



/-! ## The lower-order and strict-boundary filtrations -/



@[simp]
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl







theorem card_lowerOrder_edges_le
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

















/-! ## Main-density products -/













/-! ## The main product under duplication -/













end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
/-!
# Relative generalized counting for closed hypergraph bundles

This file performs the double induction in Tao's generalized counting
lemma.  Its sole analytic input is `HasTaoBundleCountingStep`: at one
maximal occurrence edge, the count differs from the main density times
the erased count by the square root of two lower-order counts plus the
common frozen-uniformity error.

The induction first decreases bundle order and then, at fixed order,
decreases the number of occurrence edges.  The exact main-product
identities from `HypergraphBundleGeneralizedCounting` cancel every
lower-order density from the relative defect error.  Consequently the
defect term pays only the selected-rank floor `α`, while the absolute
uniform term pays the all-rank floor `μ`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
/-! ## Canonical pullbacks on subbundles -/
/-! ## Structural bounds for the two outer-induction bundles -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- The duplicated lower-order bundle has at most twice as many edges as
the original bundle. -/
theorem solution
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).edges.card ≤
      2 * B.edges.card := by
  calc
    ((B.lowerOrder g₀.card).duplicateOutside g₀).edges.card =
        ((B.lowerOrder g₀.card).doubledEdges g₀).card := by
      rfl
    _ ≤
        2 *
          ((B.lowerOrder g₀.card).edges.erase g₀).card :=
      (B.lowerOrder g₀.card).card_doubledEdges_le g₀
    _ ≤ 2 * (B.lowerOrder g₀.card).edges.card :=
      Nat.mul_le_mul_left 2
        Finset.card_erase_le
    _ ≤ 2 * B.edges.card :=
      Nat.mul_le_mul_left 2
        (B.card_lowerOrder_edges_le g₀.card)
