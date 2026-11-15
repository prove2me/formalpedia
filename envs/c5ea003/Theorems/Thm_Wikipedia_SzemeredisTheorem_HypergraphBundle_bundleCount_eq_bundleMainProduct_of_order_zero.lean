-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_bundleCount_eq_bundleMainProduct_of_order_zero
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleCount_eq_bundleMainProduct_of_order_zero
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:31.660168+00:00
-- url     : https://prove2.me/theorems/17c4acde-efc5-45bc-acfd-b0dafcf2d651
-- title:
--   Exact bundle counts in order zero
-- statement:
--   Let $B$ be a hypergraph bundle of order zero, with finite occurrence type and finite nonempty value type. If the empty-edge base weight is identically $1$ and the empty-edge density is $p(\varnothing)=1$, its bundle count with pulled-back base weights equals its main-density product.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleRelativeCounting.lean#L263-L313

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleCount_eq_bundleMainProduct_of_order_zero
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (hAempty :
      ∀ y :
        {j : J // j ∈ (∅ : Finset J)} → G,
        A ∅ y = 1)
    (hpempty : p ∅ = 1)
    (horder : B.order = 0) :
    B.bundleCount (B.pullbackBaseEdgeWeight A) =
      B.bundleMainProduct p := by sorry
