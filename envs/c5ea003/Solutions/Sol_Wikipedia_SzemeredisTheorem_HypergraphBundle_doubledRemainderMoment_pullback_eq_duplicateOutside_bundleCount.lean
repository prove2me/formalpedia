-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:19:56.42545+00:00
-- url     : https://prove2.me/submissions/7c5e5177-dae1-455d-acc9-acbbd1c629a7

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledSourceProduct_doubledAssignment
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_duplicateOutside_closed
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_eraseEdge_closed_of_maximal
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_mean_splitDoubledAssignment

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Products of independent finite means

The product of normalized averages over independent finite variables is the
normalized average over their product space.  This is the finite-probability
Fubini identity used when expanding products of generalized convolutions.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized mean over a product type is the corresponding iterated
normalized mean. -/
theorem mean_prod_type
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = mean₂ F := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)





end Wikipedia.SzemeredisTheorem

end

section


/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/

namespace Wikipedia.SzemeredisTheorem



/-- The square of a normalized mean is the mean over two independent copies
of the variable. -/
theorem mean_sq_eq_mean_pair_mul
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean f ^ 2 =
      mean (fun p : Ω × Ω => f p.1 * f p.2) := by
  calc
    mean f ^ 2 = mean f * mean f := pow_two _
    _ = mean₂ (fun x y => f x * f y) := by
      unfold mean₂ mean
      exact
        Finset.expect_mul_expect
          Finset.univ Finset.univ f f
    _ = mean (fun p : Ω × Ω => f p.1 * f p.2) :=
      (mean_prod_type fun x y => f x * f y).symm

/-- Squaring an inner mean duplicates its variable under the outer mean. -/
theorem mean_inner_sq_eq_mean₂_pair
    {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℝ) :
    mean (fun x => mean (F x) ^ 2) =
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  unfold mean₂
  apply congrArg mean
  funext x
  exact mean_sq_eq_mean_pair_mul (F x)











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

























/-! ## Localized Cauchy--Schwarz and the doubled remainder -/









/-- The doubled moment is exactly the average obtained by taking two
independent copies of every outside variable. -/
theorem doubledRemainderMoment_eq_mean₂_pair
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean₂ (fun y :
          {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          B.edgeRemainderFiber g₀ A y z.1 *
            B.edgeRemainderFiber g₀ A y z.2) := by
  unfold doubledRemainderMoment edgeRemainderAverage
  exact mean_inner_sq_eq_mean₂_pair
    (B.edgeRemainderFiber g₀ A)







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













































/-- The doubled Cauchy--Schwarz moment is a single normalized mean over
assignments on the doubled occurrence-vertex set.  The integrand is the
source-indexed product, so the identity is valid even when the two copies
of an edge contained in `g₀` coincide as `Finset`s. -/
theorem doubledRemainderMoment_eq_mean_doubledSourceProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean (B.doubledSourceProduct g₀ A) := by
  rw [B.doubledRemainderMoment_eq_mean₂_pair]
  rw [mean_splitDoubledAssignment]
  simp_rw [B.doubledSourceProduct_doubledAssignment]















@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl





























/-- Erasing a maximum edge from a downward-closed bundle and then doubling
preserves downward closure. -/
theorem duplicateOutside_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion :=
  B.duplicateOutside_closed g₀
    (B.eraseEdge_closed_of_maximal
      hclosed hg₀ hmax)

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
/-- Consequently the doubled Cauchy--Schwarz remainder moment is the
ordinary count of the duplicated bundle for pulled-back indicator
weights.  Downward closure and maximality ensure that this duplicated
bundle remains a downward-closed bundle of no larger order. -/
theorem solution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) =
      (B.duplicateOutside g₀).bundleCount
        ((B.duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  have _hduplicateClosed :
      (B.duplicateOutside g₀).IsClosedUnderInclusion :=
    B.duplicateOutside_closed_of_maximal
      hclosed hg₀ hmax
  rw [B.doubledRemainderMoment_eq_mean_doubledSourceProduct]
  unfold bundleCount
  apply congrArg mean
  funext x
  exact
    B.doubledSourceProduct_pullback_eq_duplicateOutside_bundleProduct
      g₀ A hA x
