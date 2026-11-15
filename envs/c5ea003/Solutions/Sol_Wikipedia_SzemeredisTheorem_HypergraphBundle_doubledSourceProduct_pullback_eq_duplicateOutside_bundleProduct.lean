-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:16:02.332258+00:00
-- url     : https://prove2.me/submissions/de650adc-801d-41ee-9376-4901c57c6999

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_prod_comp_eq_prod_image_of_idempotent
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pullbackBaseEdgeWeight_duplicateOutside_doubledEdge

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



















/-! ## Local tuples and pulled-back base weights -/













@[simp]
theorem pullbackBaseEdgeWeight_of_mem
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      A (g.image B.projection)
        (B.projectedEdgeTuple hg y) := by
  classical
  simp [pullbackBaseEdgeWeight, hg]



/-! ## Bundle products and normalized counts -/





























/-! ## Freezing the outside variables -/

























/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section


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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}





























































@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl































end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Indicator weights on a duplicated hypergraph bundle

The source-indexed doubled product retains both labelled copies of every
remaining occurrence edge.  The ordinary duplicated bundle instead stores
the image of the source-edge map, so it identifies the two copies of an edge
contained in the shared edge.  For pulled-back zero--one base weights this
identification does not change the product: the only lost multiplicity is a
repeated idempotent factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}



















/-- A source factor is the factor attached to its actual doubled edge. -/
theorem doubledBundleEdgeFactor_doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (s : B.DoubledEdgeSource g₀) :
    B.doubledBundleEdgeFactor g₀ A x
        (B.doubledEdgeOfSource g₀ s) =
      B.pullbackBaseEdgeWeight A s.2.1
        (fun v =>
          x (doubledVertexLift g₀ s.1 v.1)) := by
  exact
    B.pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
      g₀ A s.1 s.2.2 x

/-- Every actual doubled-edge factor is idempotent when the base weights
are idempotent. -/
theorem doubledBundleEdgeFactor_idempotent
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀))
    (hd : d ∈ B.doubledEdges g₀) :
    B.doubledBundleEdgeFactor g₀ A x d *
        B.doubledBundleEdgeFactor g₀ A x d =
      B.doubledBundleEdgeFactor g₀ A x d := by
  classical
  unfold doubledBundleEdgeFactor
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd]
  exact hA _ ((B.duplicateOutside g₀).projection_mem_base d hd) _





end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
/-!
# Indicator weights on a duplicated hypergraph bundle

The source-indexed doubled product retains both labelled copies of every
remaining occurrence edge.  The ordinary duplicated bundle instead stores
the image of the source-edge map, so it identifies the two copies of an edge
contained in the shared edge.  For pulled-back zero--one base weights this
identification does not change the product: the only lost multiplicity is a
repeated idempotent factor.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- For indicator base weights, the source-indexed doubled product is
exactly the ordinary bundle product of the duplicated bundle. -/
theorem solution
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A)
    (x : DoubledOccurrenceVertex g₀ → G) :
    B.doubledSourceProduct g₀
        (B.pullbackBaseEdgeWeight A) x =
      (B.duplicateOutside g₀).bundleProduct
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
  classical
  unfold doubledSourceProduct
  calc
    (∏ s : B.DoubledEdgeSource g₀,
        B.pullbackBaseEdgeWeight A s.2.1
          (fun v =>
            x (doubledVertexLift g₀ s.1 v.1))) =
        ∏ s : B.DoubledEdgeSource g₀,
          B.doubledBundleEdgeFactor g₀ A x
            (B.doubledEdgeOfSource g₀ s) := by
      apply Finset.prod_congr rfl
      intro s _hs
      exact
        (B.doubledBundleEdgeFactor_doubledEdgeOfSource
          g₀ A x s).symm
    _ =
        ∏ d ∈
            (Finset.univ :
              Finset (B.DoubledEdgeSource g₀)).image
                (B.doubledEdgeOfSource g₀),
          B.doubledBundleEdgeFactor g₀ A x d := by
      apply prod_comp_eq_prod_image_of_idempotent
      intro d hd
      apply B.doubledBundleEdgeFactor_idempotent
        g₀ A hA x d
      simpa [doubledEdges] using hd
    _ =
        (B.duplicateOutside g₀).bundleProduct
          ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) x := by
      rfl
