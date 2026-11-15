-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:24.808082+00:00
-- url     : https://prove2.me/theorems/b33b3551-6269-4846-a261-60d0e13697ba
-- title:
--   A square-root bound for a selected bundle-edge contribution
-- statement:
--   Let $B$ be a downward-closed hypergraph bundle with finite occurrence vertices $K$ and finite nonempty value type $G$, and let $g_0$ be an edge of maximal cardinality. Let the base weights $A$ lie in $[0,1]$ and be idempotent. If $\beta\ge0$ and the mean of $q^2$ on assignments to $g_0$ is at most $\beta$ times the strict-boundary bundle count, then the absolute selected-edge contribution of $q$ is bounded by the square root of the product of that upper bound and the bundle count of the lower-order bundle duplicated outside $g_0$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleGeneralizedCounting.lean#L634-L719

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    {β : ℝ} (hβ : 0 ≤ β)
    (hlocalized :
      mean (fun y => q y ^ 2) ≤
        β *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) :
    |B.edgeContribution g₀ q
        (B.pullbackBaseEdgeWeight A)| ≤
      Real.sqrt
        ((β *
            (B.strictBoundary g₀).bundleCount
              ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) *
          ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
              (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)) := by sorry
