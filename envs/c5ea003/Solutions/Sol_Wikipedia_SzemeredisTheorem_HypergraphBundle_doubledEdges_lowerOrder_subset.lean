-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledEdges_lowerOrder_subset
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:16:02.301601+00:00
-- url     : https://prove2.me/submissions/b1923efc-5ee1-41b5-8885-2f32b92dae1a

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
theorem mem_lowerOrder_edges
    (B : HypergraphBundle J K H)
    (d : ℕ) (g : Finset K) :
    g ∈ (B.lowerOrder d).edges ↔
      g ∈ B.edges ∧ g.card < d := by
  simp [lowerOrder]























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
/-! ## Discarding the other maximal-rank factors -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- The doubled lower-order edge family is a subfamily of the full
doubled remainder edge family. -/
theorem solution
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.lowerOrder g₀.card).doubledEdges g₀ ⊆
      B.doubledEdges g₀ := by
  intro d hd
  obtain ⟨copy, g, hg, hgd⟩ :=
    ((B.lowerOrder g₀.card).mem_doubledEdges_iff
      g₀ d).1 hd
  apply (B.mem_doubledEdges_iff g₀ d).2
  refine ⟨copy, g, ?_, hgd⟩
  have hgLower :
      g ∈ (B.lowerOrder g₀.card).edges :=
    Finset.mem_of_mem_erase hg
  exact Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hg).1,
      ((B.mem_lowerOrder_edges g₀.card g).1
        hgLower).1⟩
