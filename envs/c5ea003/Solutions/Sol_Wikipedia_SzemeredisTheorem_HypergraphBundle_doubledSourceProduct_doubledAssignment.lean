-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledSourceProduct_doubledAssignment
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:11:52.674362+00:00
-- url     : https://prove2.me/submissions/8169e398-87df-4fbc-86b0-b14c09edd89c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledAssignment_lift_false
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledAssignment_lift_true

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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

























/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
/-!
# Duplicating the variables outside one bundle edge

The squared remainder in the bundle counting argument identifies the
variables on a selected edge `g₀` and takes two independent copies of every
variable outside `g₀`.  This file realizes that operation as a finite
hypergraph bundle.

An occurrence vertex in the doubled bundle is either a shared vertex of
`g₀`, or an outside vertex together with a Boolean copy label.  Every
remaining occurrence edge is lifted once into each copy.  The lift is
injective, preserves edge cardinality and projected base edges, and
therefore produces another valid bundle over the same base hypergraph.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- The source-indexed product on an assembled doubled assignment is
exactly the product of the two remainder fibers. -/
theorem solution
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    B.doubledSourceProduct g₀ A
        (doubledAssignment g₀ y z) =
      B.edgeRemainderFiber g₀ A y z.1 *
        B.edgeRemainderFiber g₀ A y z.2 := by
  classical
  unfold doubledSourceProduct
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp_rw [doubledAssignment_lift_true,
    doubledAssignment_lift_false]
  have hfalse :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.1) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))))
  have htrue :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.2) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))))
  rw [htrue, hfalse]
  unfold edgeRemainderFiber edgeRemainder bundleProduct
  rw [mul_comm]
  rfl
