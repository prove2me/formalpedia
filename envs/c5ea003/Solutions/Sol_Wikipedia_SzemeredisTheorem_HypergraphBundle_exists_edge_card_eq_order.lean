-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.exists_edge_card_eq_order
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:21:01.315381+00:00
-- url     : https://prove2.me/submissions/4180e9eb-a7ee-4710-b849-5c9428e6aaab

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
/-! ## Elementary main-product and induction helpers -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- A bundle of positive order has a maximal occurrence edge which
realizes its order. -/
theorem solution
    (B : HypergraphBundle J K H)
    (horder : 0 < B.order) :
    ∃ g₀ ∈ B.edges,
      g₀.card = B.order ∧
        ∀ g ∈ B.edges, g.card ≤ g₀.card := by
  have hedges : B.edges.Nonempty := by
    by_contra hempty
    have hbe : B.edges = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    simp [order, hbe] at horder
  obtain ⟨g₀, hg₀, hsup⟩ :=
    Finset.exists_mem_eq_sup B.edges hedges Finset.card
  refine ⟨g₀, hg₀, ?_, ?_⟩
  · simpa [order] using hsup.symm
  · intro g hg
    rw [← hsup]
    exact Finset.le_sup hg
