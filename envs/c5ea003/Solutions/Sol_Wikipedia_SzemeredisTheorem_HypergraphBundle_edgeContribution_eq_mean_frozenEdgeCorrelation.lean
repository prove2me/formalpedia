-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.edgeContribution_eq_mean_frozenEdgeCorrelation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:44.3859+00:00
-- url     : https://prove2.me/submissions/48ff6052-6c7d-4225-bdce-d408614f650f

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_mean_splitEdge

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

































theorem mean₂_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean₂ f = mean₂ (fun y x => f x y) := by
  exact Finset.expect_comm Finset.univ Finset.univ f

end Wikipedia.SzemeredisTheorem

end

section



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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}











@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl







/-! ## Local tuples and pulled-back base weights -/

















/-! ## Bundle products and normalized counts -/





























/-! ## Freezing the outside variables -/







@[simp]
theorem splitEdgeEquiv_fst
    (g : Finset K) (x : K → G) :
    (splitEdgeEquiv g x).1 = edgeTuple g x := by
  funext v
  simp [splitEdgeEquiv, edgeSumEquiv, edgeTuple]

/-- Recombining a selected-edge tuple and an outside tuple recovers the
selected-edge tuple on restriction. -/
@[simp]
theorem edgeTuple_splitEdgeEquiv_symm
    (g : Finset K)
    (y : {v : K // v ∈ g} → G)
    (z : EdgeComplement g → G) :
    edgeTuple g ((splitEdgeEquiv g).symm (y, z)) = y := by
  rw [← splitEdgeEquiv_fst]
  simp















/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- The selected-edge contribution is the outside average of the
correlations obtained by freezing the outside variables. -/
theorem solution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (B.frozenEdgeCorrelation g₀ q A) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀, mean₂_comm]
  unfold frozenEdgeCorrelation edgeRemainderFiber mean₂
  apply congrArg mean
  funext z
  apply congrArg mean
  funext y
  change
    q (edgeTuple g₀
        ((splitEdgeEquiv g₀).symm (y, z))) *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z)) =
      q y *
        B.edgeRemainder g₀ A
          ((splitEdgeEquiv g₀).symm (y, z))
  rw [edgeTuple_splitEdgeEquiv_symm]
