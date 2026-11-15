-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:26:06.660132+00:00
-- url     : https://prove2.me/submissions/bc66962e-1de7-4030-b4a0-cd4d9b56b450

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_duplicateOutside_bundleProduct_le_lowerOrder
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_mean_splitEdge

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/

namespace Wikipedia.SzemeredisTheorem

/-- Global Cauchy--Schwarz for a normalized finite mean. -/
theorem mean_mul_sq_le_product
    {Ω : Type*} [Fintype Ω]
    (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) *
        mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)















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

/-- Pullback preserves unit-interval bounds on every bundle edge. -/
theorem pullbackBaseEdgeWeight_unitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    0 ≤ B.pullbackBaseEdgeWeight A g y ∧
      B.pullbackBaseEdgeWeight A g y ≤ 1 := by
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _

/-! ## Bundle products and normalized counts -/



/-- Pulling back a bounded base family gives a bounded bundle family. -/
theorem pullbackBaseEdgeWeight_weightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsInUnitInterval H A) :
    B.WeightsInUnitInterval
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  exact B.pullbackBaseEdgeWeight_unitInterval A hA hg y





theorem bundleProduct_nonneg
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (x : K → G) :
    0 ≤ B.bundleProduct A x := by
  unfold bundleProduct
  exact Finset.prod_nonneg fun g hg =>
    (hA g hg (edgeTuple g x)).1



theorem bundleCount_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A) :
    0 ≤ B.bundleCount A :=
  mean_nonneg (B.bundleProduct_nonneg hA)















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







/-- A selected-edge contribution is the pairing of its local function with
the conditional average of all remaining factors. -/
theorem edgeContribution_eq_mean_mul_remainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A =
      mean (fun y =>
        q y * B.edgeRemainderAverage g₀ A y) := by
  unfold edgeContribution
  rw [mean_splitEdge g₀]
  unfold mean₂ edgeRemainderAverage edgeRemainderFiber
  apply congrArg mean
  funext y
  simp only [edgeTuple_splitEdgeEquiv_symm]
  rw [mean_smul]







/-! ## Localized Cauchy--Schwarz and the doubled remainder -/



theorem doubledRemainderMoment_nonneg
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    0 ≤ B.doubledRemainderMoment g₀ A :=
  mean_nonneg fun _ => sq_nonneg _







/-- Cauchy--Schwarz bounds a selected-edge contribution by the local square
mass of its edge term times the doubled lower-rank remainder moment. -/
theorem edgeContribution_sq_le_localSquare_mul_doubled
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ q A ^ 2 ≤
      mean (fun y => q y ^ 2) *
        B.doubledRemainderMoment g₀ A := by
  rw [B.edgeContribution_eq_mean_mul_remainderAverage]
  exact mean_mul_sq_le_product q
    (B.edgeRemainderAverage g₀ A)





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
# Filtrations of hypergraph bundles

The generalized counting argument repeatedly discards all edges of the
current maximal rank and then duplicates the remaining bundle around one
selected maximal edge.  This file packages the elementary structural
operations used in that step.

Besides arbitrary edge filtering, we single out the lower-order part of a
bundle and the strict boundary below a fixed edge.  The final product
identity records the only collisions caused by duplication: the two
labelled copies of a strict boundary edge coincide, whereas every other
lower-order edge contributes two distinct copies.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Edge-filtered subbundles -/















/-! ## The lower-order and strict-boundary filtrations -/



@[simp]
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl













@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl











/-! ## Main-density products -/













/-! ## The main product under duplication -/













end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section



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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Local strict-boundary products -/





















/-! ## Main-product cancellation at a selected edge -/























/-! ## Discarding the other maximal-rank factors -/







/-- **Maximal-factor discard.**  For indicator base weights, the exact
doubled remainder moment is bounded by the count of the duplicated
lower-order bundle. -/
theorem doubledRemainderMoment_pullback_le_lowerOrder
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A) :
    B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
          (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A) := by
  rw [B.doubledRemainderMoment_pullback_eq_duplicateOutside_bundleCount
    hclosed hg₀ hmax A hAidempotent]
  unfold bundleCount
  apply mean_mono
  intro x
  exact B.duplicateOutside_bundleProduct_le_lowerOrder
    g₀ A hA01 x



end HypergraphBundle

/-! ## Numerical envelope for the double induction -/









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
/-- A localized defect square bound and the maximal-factor discard give
the source-faithful square-root defect estimate.  The two lower-order
counts in this statement are precisely the two outer-induction calls. -/
theorem solution
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (A : BaseEdgeWeight J G)
    (hA01 : BaseWeightsInUnitInterval H A)
    (hAidempotent : BaseWeightsIdempotent H A)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    {β : ℝ} (hβ : 0 ≤ β)
    (hlocalized :
      mean (fun y => q y ^ 2) ≤
        β *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) :
    |B.edgeContribution g₀ q
        (B.pullbackBaseEdgeWeight A)| ≤
      Real.sqrt
        ((β *
            (B.strictBoundary g₀).bundleCount
              ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)) *
          ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
              (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)) := by
  let boundaryCount :=
    (B.strictBoundary g₀).bundleCount
      ((B.strictBoundary g₀).pullbackBaseEdgeWeight A)
  let lowerDoubledCount :=
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
        (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight A)
  have hboundary0 : 0 ≤ boundaryCount := by
    apply (B.strictBoundary g₀).bundleCount_nonneg
    exact
      (B.strictBoundary g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hlower0 : 0 ≤ lowerDoubledCount := by
    apply
      ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount_nonneg
    exact
      ((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight_weightsInUnitInterval
          A hA01
  have hmoment0 :
      0 ≤ B.doubledRemainderMoment g₀
        (B.pullbackBaseEdgeWeight A) :=
    B.doubledRemainderMoment_nonneg g₀
      (B.pullbackBaseEdgeWeight A)
  have hmoment :
      B.doubledRemainderMoment g₀
          (B.pullbackBaseEdgeWeight A) ≤
        lowerDoubledCount :=
    B.doubledRemainderMoment_pullback_le_lowerOrder
      hclosed hg₀ hmax A hA01 hAidempotent
  have hsq :
      B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A) ^ 2 ≤
        (β * boundaryCount) * lowerDoubledCount := by
    calc
      B.edgeContribution g₀ q
            (B.pullbackBaseEdgeWeight A) ^ 2 ≤
          mean (fun y => q y ^ 2) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        B.edgeContribution_sq_le_localSquare_mul_doubled
          g₀ q (B.pullbackBaseEdgeWeight A)
      _ ≤
          (β * boundaryCount) *
            B.doubledRemainderMoment g₀
              (B.pullbackBaseEdgeWeight A) :=
        mul_le_mul_of_nonneg_right hlocalized hmoment0
      _ ≤ (β * boundaryCount) * lowerDoubledCount :=
        mul_le_mul_of_nonneg_left hmoment
          (mul_nonneg hβ hboundary0)
  have hradicand :
      0 ≤ (β * boundaryCount) * lowerDoubledCount :=
    mul_nonneg (mul_nonneg hβ hboundary0) hlower0
  apply
    (sq_le_sq₀
      (abs_nonneg
        (B.edgeContribution g₀ q
          (B.pullbackBaseEdgeWeight A)))
      (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hradicand]
  exact hsq
