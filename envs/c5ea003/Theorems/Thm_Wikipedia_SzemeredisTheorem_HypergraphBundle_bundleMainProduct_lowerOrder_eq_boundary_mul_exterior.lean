-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:28.432546+00:00
-- url     : https://prove2.me/theorems/197bd891-2dd4-4805-9ad5-3ba5b38bb02f
-- title:
--   Splitting a lower-order main product into boundary and exterior
-- statement:
--   For a hypergraph bundle $B$, a selected vertex set $g_0$, and a real base-density function $p$, the main-density product of the subbundle of order below $|g_0|$ equals the strict-boundary main product times the lower-exterior main product relative to $g_0$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleGeneralizedCounting.lean#L294-L336

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleMainProduct_lowerOrder_eq_boundary_mul_exterior
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) :
    (B.lowerOrder g₀.card).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
        B.lowerExteriorMainProduct g₀ p := by sorry
