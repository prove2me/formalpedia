-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_eraseEdge_closed_of_maximal
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.eraseEdge_closed_of_maximal
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:32:57.689974+00:00
-- url     : https://prove2.me/theorems/7736f040-58c8-40c9-b5e7-0c86b60fecb5
-- title:
--   Erasing a maximal edge preserves downward closure
-- statement:
--   Let $B$ be a hypergraph bundle closed under inclusion. If $g_0$ is an edge whose cardinality is at least that of every edge of $B$, then the bundle obtained by erasing $g_0$ is still closed under inclusion.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleCounting.lean#L127-L148

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.eraseEdge_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (_hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.eraseEdge g₀).IsClosedUnderInclusion := by sorry
