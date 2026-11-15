-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_bundleCount_decompose_edge
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleCount_decompose_edge
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:25.507783+00:00
-- url     : https://prove2.me/theorems/5120b20d-78bd-46b7-b105-471b315cbb2e
-- title:
--   Decomposition of a bundle count at one edge
-- statement:
--   Let $B$ be a hypergraph bundle with finite occurrence and value types, and let $g_0$ be one of its edges. If its edge weight decomposes pointwise as $A_{g_0}=p+b+c$, where $p\in\mathbb R$, then the bundle count equals $p$ times the count with $g_0$ erased, plus the selected-edge contribution of $b$, plus that of $c$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleCounting.lean#L367-L412

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Hypergraph bundles and the counting-lemma decomposition

Tao's hypergraph counting lemma is proved after passing from one copy of
each vertex class to a *hypergraph bundle*.  A bundle has a finite set of
occurrence vertices, a finite family of occurrence edges, and a projection
to the base vertex classes which is injective on every occurrence edge.
The extra occurrence vertices record the copies created by repeated
Cauchy--Schwarz.

This file supplies the finite bundle object and the exact analytic
identities at one step of the double induction.  For a selected edge `g₀`,
the bundle count is split according to

```
edgeWeight = main + defect + uniform.
```

The uniform contribution is rewritten by freezing all variables outside
`g₀`.  The defect contribution is bounded by Cauchy--Schwarz; the second
factor is written exactly as an average with two independent copies of the
outside variables.  This is the doubled lower-rank bundle appearing in
Tao's proof.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
/-! ## Local tuples and pulled-back base weights -/
/-! ## Bundle products and normalized counts -/

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleCount_decompose_edge
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (p : ℝ)
    (b c : ({v : K // v ∈ g₀} → G) → ℝ)
    (hdecomp : ∀ y, A g₀ y = p + b y + c y) :
    B.bundleCount A =
      p * (B.eraseEdge g₀).bundleCount A +
        B.edgeContribution g₀ b A +
        B.edgeContribution g₀ c A := by sorry
