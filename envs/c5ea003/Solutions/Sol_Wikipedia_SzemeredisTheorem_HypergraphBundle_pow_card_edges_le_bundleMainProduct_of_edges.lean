-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.pow_card_edges_le_bundleMainProduct_of_edges
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:21:01.453196+00:00
-- url     : https://prove2.me/submissions/7fc95c69-54e3-4bc7-94f5-0a9e0d9cb8f7

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
/-- It is enough to check a density floor on the actual occurrence edges
of a bundle. -/
theorem solution
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ g ∈ B.edges,
        a ≤ p (g.image B.projection)) :
    a ^ B.edges.card ≤ B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  calc
    a ^ B.edges.card =
        ∏ _g ∈ B.edges, a := by
      simp
    _ ≤
        ∏ g ∈ B.edges,
          p (g.image B.projection) := by
      apply Finset.prod_le_prod
      · intro g hg
        exact ha
      · intro g hg
        exact hp g hg
