-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:54:00.808543+00:00
-- url     : https://prove2.me/theorems/35dcf098-3fc9-4bbe-99b1-5257eeee475f
-- title:
--   The maximal-edge step required by relative bundle counting
-- statement:
--   For fixed base-edge weights, base densities, a rank-dependent real error function $\beta$, and a real remainder $\tau$, this predicate requires a one-edge estimate for every finite occurrence bundle closed under inclusion and every maximal-cardinality occurrence edge.
--
--   The estimate compares the bundle count with the selected edge's base density times the count after erasing that edge. Its error is at most $\tau$ plus the square root of $\beta$ at the edge rank times two lower-order counts: the strict-boundary bundle count and the duplicated lower-order bundle count. The predicate states this analytic step explicitly; it does not insert an induction hypothesis or a hidden density normalization.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleRelativeCounting.lean#L325-L348

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Canonical pullbacks on subbundles -/







/-! ## Structural bounds for the two outer-induction bundles -/







/-! ## Elementary main-product and induction helpers -/











end HypergraphBundle

/-! ## The analytic one-edge interface -/

universe uJ uG

variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}

/-- The exact analytic output of one maximal-edge step in Tao's bundle
counting proof.  No induction estimate or density normalization is hidden
in this hypothesis. -/
def HasTaoBundleCountingStep
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (β : ℕ → ℝ) (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, g₀ ∈ B.edges →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      |B.bundleCount (B.pullbackBaseEdgeWeight A) -
          p (g₀.image B.projection) *
            (B.eraseEdge g₀).bundleCount
              ((B.eraseEdge g₀).pullbackBaseEdgeWeight A)| ≤
        Real.sqrt
            (β g₀.card *
              (B.strictBoundary g₀).bundleCount
                ((B.strictBoundary g₀).pullbackBaseEdgeWeight A) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                  A)) +
          τ

/-! ## Full double induction -/



end Wikipedia.SzemeredisTheorem


