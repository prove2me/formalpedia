-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.pullbackBaseEdgeWeight_eq_of_projection_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:05.833844+00:00
-- url     : https://prove2.me/submissions/218269c7-8cc2-40e9-b712-e072e6b80a3b

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



















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
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
/-! ## Discarding the other maximal-rank factors -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- Pullbacks through two bundles with the same occurrence projection
agree on every edge common to the two bundles. -/
theorem solution
    (B C : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hprojection : B.projection = C.projection)
    {g : Finset K}
    (hgB : g ∈ B.edges) (hgC : g ∈ C.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      C.pullbackBaseEdgeWeight A g y := by
  classical
  rw [B.pullbackBaseEdgeWeight_of_mem A hgB y,
    C.pullbackBaseEdgeWeight_of_mem A hgC y]
  have himage :
      g.image B.projection = g.image C.projection :=
    congrArg (fun q : K → J => g.image q) hprojection
  let lhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image B.projection,
      B.projectedEdgeTuple hgB y⟩
  let rhsInput :
      (Σ e : Finset J,
        ({j : J // j ∈ e} → G)) :=
    ⟨g.image C.projection,
      C.projectedEdgeTuple hgC y⟩
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
  let jB :
      {j : J // j ∈ g.image B.projection} :=
    (finsetMembershipEquivOfEq himage).symm j
  let vB := (B.projectionEquiv hgB).symm jB
  let vC := (C.projectionEquiv hgC).symm j
  have hjB : jB.1 = j.1 :=
    finsetMembershipEquivOfEq_symm_val himage j
  have hvB :
      B.projection vB.1 = jB.1 := by
    exact congrArg Subtype.val
      ((B.projectionEquiv hgB).apply_symm_apply jB)
  have hvC' :
      C.projection vC.1 = j.1 := by
    exact congrArg Subtype.val
      ((C.projectionEquiv hgC).apply_symm_apply j)
  have hvC :
      B.projection vC.1 = j.1 := by
    rw [hprojection]
    exact hvC'
  have hval : vB.1 = vC.1 :=
    B.projection_injective_on_edge g hgB
      vB.2 vC.2
      ((hvB.trans hjB).trans hvC.symm)
  unfold lhsInput rhsInput projectedEdgeTuple
  change y vB = y vC
  exact congrArg y (Subtype.ext hval)
