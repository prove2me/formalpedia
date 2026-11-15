-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pow_card_edges_le_bundleMainProduct_of_edges
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.pow_card_edges_le_bundleMainProduct_of_edges
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:05.462272+00:00
-- url     : https://prove2.me/theorems/bc0997a8-45d9-40d1-ba52-c97522028ec4
-- title:
--   An edgewise density floor bounds the main product
-- statement:
--   Let $B$ be a hypergraph bundle and $p$ a real base-density function. If $a\ge0$ and $p$ is at least $a$ on the projected image of every occurrence edge of $B$, then $a^{|B.\mathrm{edges}|}$ is at most the main-density product of $B$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleRelativeCounting.lean#L183-L206

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.pow_card_edges_le_bundleMainProduct_of_edges
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ g ∈ B.edges,
        a ≤ p (g.image B.projection)) :
    a ^ B.edges.card ≤ B.bundleMainProduct p := by sorry
