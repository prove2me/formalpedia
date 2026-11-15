-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleMainProduct_duplicateOutside_lowerOrder
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:19:56.354196+00:00
-- url     : https://prove2.me/submissions/da3b3c40-3fdb-4990-b6fb-b22dc47363f5

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_bundleMainProduct_duplicateOutside

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



@[simp]
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl













@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl











/-! ## Main-density products -/













/-! ## The main product under duplication -/













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
/-- **Lower-order duplication identity.**  Duplicating the lower-order
subbundle around `g₀` contributes one copy of every strict-boundary
density and the square of every other lower-order density. -/
theorem solution
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
      ∏ g ∈ B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  rw [(B.lowerOrder g₀.card).bundleMainProduct_duplicateOutside g₀ p]
  have hg₀' :
      g₀ ∉ B.edges.filter (fun g => g.card < g₀.card) := by
    simp
  have hboundary :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB,
        Finset.card_lt_card hgstrict⟩, hgstrict.1⟩
  have hexterior :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    tauto
  simp only [lowerOrder, strictBoundary,
    filterEdges, bundleMainProduct]
  rw [Finset.erase_eq_of_notMem hg₀',
    hboundary, hexterior]
