-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:15:58.983201+00:00
-- url     : https://prove2.me/submissions/053a9510-5cbc-4124-b50f-fbf7875c11b3

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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
# Generalized counting for closed hypergraph bundles

This file packages the part of Tao's generalized counting argument which
is specific to hypergraph bundles.

There are two points which are easy to lose in a scalar recurrence.

* The defect at a selected maximal edge is localized to the product of
  the strict-boundary indicators.  Since those indicators already occur
  among the remaining bundle factors, idempotence lets us insert that
  boundary product without changing the contribution.
* After Cauchy--Schwarz, all remaining maximal-rank indicator factors may
  be discarded.  The resulting moment is the count of the duplicated
  lower-order bundle.  Its main-density product contains one copy of the
  strict boundary and two copies of every other lower-order edge.

The last section records a flexible numerical envelope for the ensuing
double induction.  It deliberately separates the same-rank density floor
`α` from the all-rank density floor `μ`: the defect term only loses powers
of `α`, while the common frozen-uniformity error may lose powers of `μ`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
/-! ## Local strict-boundary products -/
/-! ## Main-product cancellation at a selected edge -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- The lower-order main product splits into the strict boundary and the
lower-order exterior. -/
theorem solution
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
        B.lowerExteriorMainProduct g₀ p := by
  classical
  let s :=
    B.edges.filter
      (fun g => g.card < g₀.card)
  have hboundary :
      s.filter (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB, Finset.card_lt_card hgstrict⟩,
        hgstrict.1⟩
  have hexterior :
      s.filter (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g =>
            g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [s, Finset.mem_filter]
    tauto
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  unfold bundleMainProduct lowerExteriorMainProduct
  simp only [lowerOrder_edges, strictBoundary_edges]
  rw [← hboundary, ← hexterior]
  exact hsplit.symm
