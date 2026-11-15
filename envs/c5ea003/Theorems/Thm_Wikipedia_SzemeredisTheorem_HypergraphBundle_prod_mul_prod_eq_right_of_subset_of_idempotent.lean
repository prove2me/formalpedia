-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_prod_mul_prod_eq_right_of_subset_of_idempotent
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.prod_mul_prod_eq_right_of_subset_of_idempotent
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:08.820834+00:00
-- url     : https://prove2.me/theorems/20ec5cda-f4b5-4599-b94d-bb393a648d33
-- title:
--   An idempotent subproduct is absorbed by a containing product
-- statement:
--   Let $s\subseteq t$ be finite sets and let $f$ be real-valued. If $f(i)^2=f(i)$ for every $i\in s$, then $(\prod_{i\in s}f(i))(\prod_{i\in t}f(i))=\prod_{i\in t}f(i)$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleGeneralizedCounting.lean#L140-L180

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.prod_mul_prod_eq_right_of_subset_of_idempotent
    {ι : Type*}
    (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t)
    (hf : ∀ i ∈ s, f i * f i = f i) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) =
      ∏ i ∈ t, f i := by sorry
