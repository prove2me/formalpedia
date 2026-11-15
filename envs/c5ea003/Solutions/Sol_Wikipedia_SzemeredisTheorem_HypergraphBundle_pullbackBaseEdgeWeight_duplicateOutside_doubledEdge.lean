-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.pullbackBaseEdgeWeight_duplicateOutside_doubledEdge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:01.351611+00:00
-- url     : https://prove2.me/submissions/60543894-ef3b-4a51-bacc-73cbf98c62e6

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

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

@[simp]
theorem duplicateOutside_projection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).projection =
      B.doubledProjection g₀ :=
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





@[simp]
theorem finsetMembershipEquivOfEq_symm_val
    {α : Type*} {s t : Finset α} (h : s = t)
    (a : {a : α // a ∈ t}) :
    ((finsetMembershipEquivOfEq h).symm a).1 = a.1 := by
  subst t
  rfl

/-- Transporting a function on a finite-set membership subtype amounts to
precomposing with the inverse membership transport. -/
theorem cast_finsetPi_apply
    {α G' : Type*} {s t : Finset α} (h : s = t)
    (f : {a : α // a ∈ s} → G')
    (a : {a : α // a ∈ t}) :
    cast
        (congrArg
          (fun u : Finset α =>
            ({a : α // a ∈ u} → G'))
          h)
        f a =
      f ((finsetMembershipEquivOfEq h).symm a) := by
  subst t
  rfl

/-- The forward map of `projectionEquiv` is the bundle projection. -/
@[simp]
theorem projectionEquiv_apply_val
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (v : {v : K // v ∈ g}) :
    ((B.projectionEquiv hg) v).1 =
      B.projection v.1 := by
  rfl

















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
/-- Evaluating a pulled-back base weight on a lifted occurrence edge agrees
with evaluating the original pulled-back weight on its labelled source. -/
theorem solution
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (copy : Bool) {g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (x : DoubledOccurrenceVertex g₀ → G) :
    (B.duplicateOutside g₀).pullbackBaseEdgeWeight A
        (doubledEdge g₀ copy g)
        (edgeTuple (doubledEdge g₀ copy g) x) =
      B.pullbackBaseEdgeWeight A g
        (fun v => x (doubledVertexLift g₀ copy v.1)) := by
  classical
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have hd :
      doubledEdge g₀ copy g ∈
        (B.duplicateOutside g₀).edges := by
    exact
      (B.mem_doubledEdges_iff g₀
        (doubledEdge g₀ copy g)).2
        ⟨copy, g, hg, rfl⟩
  rw [(B.duplicateOutside g₀).pullbackBaseEdgeWeight_of_mem
      A hd,
    B.pullbackBaseEdgeWeight_of_mem A hgB]
  have himage :
      (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection =
        g.image B.projection := by
    exact B.image_doubledProjection_doubledEdge g₀ copy g
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨(doubledEdge g₀ copy g).image
        (B.duplicateOutside g₀).projection,
      (B.duplicateOutside g₀).projectedEdgeTuple hd
        (edgeTuple (doubledEdge g₀ copy g) x)⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB
        (fun v =>
          x (doubledVertexLift g₀ copy v.1))⟩
  change
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) lhsInput =
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2) rhsInput
  apply congrArg
    (fun p :
        (Σ e : Finset J,
          ({j : J // j ∈ e} → G)) =>
      A p.1 p.2)
  apply Sigma.ext himage
  apply heq_of_eqRec_eq
    (congrArg
      (fun e : Finset J =>
        ({j : J // j ∈ e} → G))
      himage)
  funext j
  change
    cast
        (congrArg
          (fun e : Finset J =>
            ({j : J // j ∈ e} → G))
          himage)
        lhsInput.2 j =
      rhsInput.2 j
  rw [cast_finsetPi_apply himage]
  let jleft :
      {j : J //
        j ∈ (doubledEdge g₀ copy g).image
          (B.duplicateOutside g₀).projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let v : {v : K // v ∈ g} :=
    (B.projectionEquiv hgB).symm j
  have hjv :
      (⟨B.projection v.1,
          Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}) = j := by
    exact
      (B.projectionEquiv hgB).apply_symm_apply j
  have hvlift :
      doubledVertexLift g₀ copy v.1 ∈
        doubledEdge g₀ copy g :=
    mem_doubledEdge g₀ copy g v.1 v.2
  have hpreimage :
      ((B.duplicateOutside g₀).projectionEquiv hd).symm jleft =
        ⟨doubledVertexLift g₀ copy v.1, hvlift⟩ := by
    apply ((B.duplicateOutside g₀).projectionEquiv hd).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    calc
      jleft.1 = j.1 := by
        exact
          finsetMembershipEquivOfEq_symm_val
            himage j
      _ = B.projection v.1 :=
        congrArg Subtype.val hjv.symm
      _ =
          (((B.duplicateOutside g₀).projectionEquiv hd)
            ⟨doubledVertexLift g₀ copy v.1,
              hvlift⟩).1 := by
        rw [projectionEquiv_apply_val,
          duplicateOutside_projection,
          doubledProjection_lift]
  unfold lhsInput rhsInput projectedEdgeTuple edgeTuple
  change
    x (((B.duplicateOutside g₀).projectionEquiv hd).symm
        jleft).1 =
      x (doubledVertexLift g₀ copy v.1)
  rw [hpreimage]
