-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pow_card_maximalRemainder_le
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.pow_card_maximalRemainder_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:01.608012+00:00
-- url     : https://prove2.me/theorems/5e83a91c-20d1-47e5-8829-d1da74f93a7c
-- title:
--   A same-rank density floor bounds the maximal remainder
-- statement:
--   Let $B$ be a hypergraph bundle and let $g_0$ be a finite vertex set whose cardinality bounds that of every edge of $B$. If $a\ge0$ and every base edge of cardinality $|g_0|$ has density at least $a$, then the maximal-remainder main product is at least $a^t$, where $t$ counts the edges other than $g_0$ that do not have smaller cardinality than $g_0$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleGeneralizedCounting.lean#L414-L456

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.pow_card_maximalRemainder_le
    (B : HypergraphBundle J K H)
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (p : Finset J → ℝ) {a : ℝ}
    (ha : 0 ≤ a)
    (hp :
      ∀ e ∈ H, e.card = g₀.card →
        a ≤ p e) :
    a ^
          ((B.edges.erase g₀).filter
            (fun g => ¬ g.card < g₀.card)).card ≤
      B.maximalRemainderMainProduct g₀ p := by sorry
