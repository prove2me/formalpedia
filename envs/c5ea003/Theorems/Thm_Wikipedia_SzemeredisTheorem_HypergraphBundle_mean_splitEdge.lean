-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_mean_splitEdge
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.mean_splitEdge
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:07.483121+00:00
-- url     : https://prove2.me/theorems/3a658fd0-6a60-4d5e-9b39-2981dd244840
-- title:
--   Fubini decomposition into an edge and its complement
-- statement:
--   Let $K,G$ be finite types, with decidable equality on $K$, and let $g\subseteq K$ be finite. For every $f:(K\to G)\to\mathbb R$, the normalized mean of $f$ equals the iterated mean over assignments on $g$ and its complement, with the two assignments assembled by the canonical splitting equivalence.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleCounting.lean#L472-L495

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
/-! ## Freezing the outside variables -/

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.mean_splitEdge
    [Fintype K] [Fintype G]
    (g : Finset K) (f : (K → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g} → G =>
        fun z : EdgeComplement g → G =>
          f ((splitEdgeEquiv g).symm (y, z))) := by sorry
