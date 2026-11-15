-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.hasTaoBundleCountingStep_orderedConfiguration
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:26:26.686107+00:00
-- url     : https://prove2.me/submissions/42b490d4-70db-482d-8d1c-0b4b91525b7e

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_bundleCount_decompose_edge
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_edgeContribution_eq_mean_frozenEdgeCorrelation
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pullbackBaseEdgeWeight_eq_of_projection_eq
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pullback_orderedConfigurationBaseWeight_decompose
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_strictBoundaryLocalProduct_mul_edgeRemainder
import Theorems.Thm_Wikipedia_SzemeredisTheorem_orderedConfigurationBaseWeight_idempotent
import Theorems.Thm_Wikipedia_SzemeredisTheorem_orderedConfigurationBaseWeight_unitInterval

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































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



/-! ## Bundle products and normalized counts -/























/-- Factoring a selected edge out of the bundle product. -/
theorem bundleCount_eq_edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    B.bundleCount A =
      B.edgeContribution g₀ (A g₀) A := by
  unfold bundleCount edgeContribution edgeRemainder
  apply congrArg mean
  funext x
  exact
    (Finset.mul_prod_erase B.edges
      (fun g => A g (edgeTuple g x)) hg₀).symm



/-- A constant local term contributes that constant times the bundle count
with the selected edge erased. -/
theorem edgeContribution_const
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (p : ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.edgeContribution g₀ (fun _ => p) A =
      p * (B.eraseEdge g₀).bundleCount A := by
  unfold edgeContribution bundleCount
  rw [← mean_smul]
  rfl

/-! ## Freezing the outside variables -/























/-- Uniform control after freezing the outside variables controls the full
uniform contribution. -/
theorem abs_edgeContribution_le_of_frozen
    [Fintype K] [Fintype G] [Nonempty G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    {ε : ℝ}
    (hfrozen :
      ∀ z, |B.frozenEdgeCorrelation g₀ q A z| ≤ ε) :
    |B.edgeContribution g₀ q A| ≤ ε := by
  rw [B.edgeContribution_eq_mean_frozenEdgeCorrelation]
  calc
    |mean (B.frozenEdgeCorrelation g₀ q A)| ≤
        mean (fun z =>
          |B.frozenEdgeCorrelation g₀ q A z|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _z : EdgeComplement g₀ → G => ε) :=
      mean_mono hfrozen
    _ = ε := mean_const _

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













/-- Pullback preserves pointwise idempotence. -/
theorem pullbackBaseEdgeWeight_weightsIdempotent
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    (hA : BaseWeightsIdempotent H A) :
    B.WeightsIdempotent
      (B.pullbackBaseEdgeWeight A) := by
  intro g hg y
  rw [B.pullbackBaseEdgeWeight_of_mem A hg y]
  exact hA _ (B.projection_mem_base g hg) _





/-- Localizing a selected-edge function to the strict boundary does not
change its contribution.  This is the exact insertion used before the
localized defect estimate. -/
theorem edgeContribution_mul_strictBoundaryLocalProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (hA : B.WeightsIdempotent A) :
    B.edgeContribution g₀ q A =
      B.edgeContribution g₀
        (fun y =>
          q y *
            B.strictBoundaryLocalProduct g₀ A y)
        A := by
  unfold edgeContribution
  apply congrArg mean
  funext x
  rw [mul_assoc,
    B.strictBoundaryLocalProduct_mul_edgeRemainder
      g₀ A hA x]

/-! ## Main-product cancellation at a selected edge -/























/-! ## Discarding the other maximal-rank factors -/











end HypergraphBundle

/-! ## Numerical envelope for the double induction -/









end Wikipedia.SzemeredisTheorem

end

section


/-!
# Relative generalized counting for closed hypergraph bundles

This file performs the double induction in Tao's generalized counting
lemma.  Its sole analytic input is `HasTaoBundleCountingStep`: at one
maximal occurrence edge, the count differs from the main density times
the erased count by the square root of two lower-order counts plus the
common frozen-uniformity error.

The induction first decreases bundle order and then, at fixed order,
decreases the number of occurrence edges.  The exact main-product
identities from `HypergraphBundleGeneralizedCounting` cancel every
lower-order density from the relative defect error.  Consequently the
defect term pays only the selected-rank floor `α`, while the absolute
uniform term pays the all-rank floor `μ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Canonical pullbacks on subbundles -/

/-- On a subbundle with the same occurrence projection, pulling a base
weight back before or after passing to the subbundle gives the same
bundle product. -/
theorem bundleProduct_pullback_eq_of_subset_of_projection_eq
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G)
    (x : K → G) :
    C.bundleProduct (B.pullbackBaseEdgeWeight A) x =
      C.bundleProduct (C.pullbackBaseEdgeWeight A) x := by
  unfold bundleProduct
  apply Finset.prod_congr rfl
  intro g hg
  exact B.pullbackBaseEdgeWeight_eq_of_projection_eq
    C A hprojection (hCB hg) hg (edgeTuple g x)

/-- Count-level version of canonical pullback invariance. -/
theorem bundleCount_pullback_eq_of_subset_of_projection_eq
    [Fintype K] [Fintype G]
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G) :
    C.bundleCount (B.pullbackBaseEdgeWeight A) =
      C.bundleCount (C.pullbackBaseEdgeWeight A) := by
  unfold bundleCount
  apply congrArg mean
  funext x
  exact B.bundleProduct_pullback_eq_of_subset_of_projection_eq
    C hCB hprojection A x

/-- In particular, the erased count may always be written using the
canonical pullback of the erased bundle. -/
theorem eraseEdge_bundleCount_pullback
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (A : BaseEdgeWeight J G) :
    (B.eraseEdge g₀).bundleCount
        (B.pullbackBaseEdgeWeight A) =
      (B.eraseEdge g₀).bundleCount
        ((B.eraseEdge g₀).pullbackBaseEdgeWeight A) := by
  apply B.bundleCount_pullback_eq_of_subset_of_projection_eq
    (B.eraseEdge g₀)
  · exact Finset.erase_subset _ _
  · rfl

/-! ## Structural bounds for the two outer-induction bundles -/







/-! ## Elementary main-product and induction helpers -/











end HypergraphBundle

/-! ## The analytic one-edge interface -/

universe uJ uG

variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}



/-! ## Full double induction -/



end Wikipedia.SzemeredisTheorem

end

section


/-!
# Bernoulli reduction for bounded boundary products

The preliminary shared-face regularity lemma is stated using Boolean
products on the immediate boundary of an upper face.  This file proves that
this loses no generality for products of arbitrary `[0,1]`-valued boundary
factors.

At successor arity the ordinary `CutTestFamily` coordinates are exactly the
boundary coordinates.  The only formal difference is that
`BooleanCutAssignment` uses an uncurried product index whereas
`BoundaryBooleanCutAssignment` is curried.  After recording the equivalence
between those two presentations, the finite Bernoulli-mixture identities
from `BooleanCutReduction` give:

* every bounded boundary factor is a convex average of Boolean component
  indicators;
* every bounded boundary product is a convex average of
  `boundaryBooleanCutSupport` indicators;
* Boolean preliminary regularity therefore controls every bounded boundary
  product with the same error.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





















/-- At successor arity the specialized boundary erasure is the ordinary
cut-test coordinate erasure. -/
theorem eraseBoundaryCoordinate_eq_eraseCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    eraseBoundaryCoordinate i x = eraseCoordinate i x :=
  rfl









namespace FaceRegularityState





end FaceRegularityState





end Wikipedia.SzemeredisTheorem

end

section





/-!
# The ordered configuration as an initial hypergraph bundle

The generalized bundle counting lemma starts from the bundle having one
occurrence vertex above each vertex class.  Its edges are the empty edge
and the ranges of all positive ordered faces.  This file identifies that
initial bundle, its indicator weights, and its main-density product with
the ordered-configuration objects used by the removal argument.

The only small bookkeeping issue is that an ordered face is an increasing
map `Fin n ↪o Fin k`, whereas a bundle edge is a `Finset (Fin k)`.  A
nonempty finite set has a unique increasing enumeration, supplied by
`Finset.orderEmbOfFin`; the equivalence below packages this canonical
change of indices.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive ordered faces as nonempty finite edges -/























/-! ## The complete initial bundle -/

















/-! ## Canonical local tuples and base weights -/







@[simp]
theorem orderedConfigurationBaseWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (y : {v : Fin k // v ∈ (∅ : Finset (Fin k))} → G) :
    orderedConfigurationBaseWeight A ∅ y = 1 := by
  simp [orderedConfigurationBaseWeight]







/-! ## Main densities -/



@[simp]
theorem orderedConfigurationBaseDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    orderedConfigurationBaseDensity P A ∅ = 1 := by
  simp [orderedConfigurationBaseDensity]





/-! ## Exact initial count and product identities -/













end Wikipedia.SzemeredisTheorem

end
/-!
# The ordered-configuration one-edge bundle step

This file isolates the last analytic bridge between ordered atom
configurations and Tao's generalized bundle-counting induction.

For a nonempty occurrence edge `g₀`, its bundle projection is a nonempty
base edge of cardinality at most `r`, hence has a canonical positive
ordered face.  Pulling the configuration indicator back to `g₀` then has
the exact mixed decomposition

```
indicator = coarse density + boundary defect + fine-boundary residual.
```

The generalized counting file already turns a boundary-localized square
estimate into the required square-root error and turns frozen correlation
bounds into the required uniform error.  The two predicates below state
exactly the remaining transport obligations.

The localized-defect predicate is deliberately *weighted by the complete
strict-boundary bundle count*.  The existing
`ClosedOrderedAtomConfiguration.IsMixedGood` estimate controls the defect
on the canonical coarse boundary atom.  Since a strict bundle boundary
also contains all lower-rank configuration factors, obtaining the
weighted statement is an additional hypothesis; it does not follow merely
by discarding factors from the unweighted localized mass.

The frozen-uniformity predicate is the combinatorial reindexing statement
that, after the outside occurrence variables are fixed, the remaining
bundle product is a bounded cut test on the selected projected face.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}
/-! ## The canonical face of a nonempty occurrence edge -/
/-! ## The transported mixed decomposition -/
/-! ## The two exact transport obligations -/
/-! ## Assembly of the one-edge input -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- The two transport obligations, together with the exact decomposition,
give the analytic one-edge hypothesis consumed by the relative generalized
bundle-counting induction. -/
theorem solution
    [Nonempty G]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hlocalized :
      HasOrderedConfigurationBundleLocalizedDefect P A β)
    (hfrozen :
      HasOrderedConfigurationBundleFrozenUniformity P A τ) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax
  by_cases hne : g₀.Nonempty
  · let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    let p :=
      orderedConfigurationBaseDensity P A
        (g₀.image B.projection)
    let b :=
      B.orderedConfigurationBundleDefect
        P A hg₀ hne
    let c :=
      B.orderedConfigurationBundleUniform
        P A hg₀ hne
    let bLocalized :=
      B.orderedConfigurationBundleLocalizedDefect
        P A hg₀ hne
    have hdecomp :
        ∀ y, W g₀ y = p + b y + c y := by
      intro y
      simpa only [W, p, b, c] using
        B.pullback_orderedConfigurationBaseWeight_decompose
          P A hg₀ hne y
    have hcount :
        B.bundleCount W =
          p * (B.eraseEdge g₀).bundleCount W +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W :=
      B.bundleCount_decompose_edge
        W hg₀ p b c hdecomp
    have herase :
        (B.eraseEdge g₀).bundleCount W =
          (B.eraseEdge g₀).bundleCount
            ((B.eraseEdge g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      exact
        B.eraseEdge_bundleCount_pullback g₀
          (orderedConfigurationBaseWeight A)
    have hIdempotent :
        B.WeightsIdempotent W := by
      exact B.pullbackBaseEdgeWeight_weightsIdempotent
        (orderedConfigurationBaseWeight A)
        (orderedConfigurationBaseWeight_idempotent A)
    have hlocalizeContribution :
        B.edgeContribution g₀ b W =
          B.edgeContribution g₀ bLocalized W := by
      change B.edgeContribution g₀ b W =
        B.edgeContribution g₀
          (fun y =>
            b y * B.strictBoundaryLocalProduct g₀ W y) W
      exact B.edgeContribution_mul_strictBoundaryLocalProduct
        g₀ b W hIdempotent
    have hdefect :
        |B.edgeContribution g₀ b W| ≤
          Real.sqrt
            ((β g₀.card *
                (B.strictBoundary g₀).bundleCount
                  ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                  (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) := by
      rw [hlocalizeContribution]
      exact
        B.abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
          hclosed hg₀ hmax
          (orderedConfigurationBaseWeight A)
          (orderedConfigurationBaseWeight_unitInterval A)
          (orderedConfigurationBaseWeight_idempotent A)
          bLocalized (hβ g₀.card)
          (hlocalized K B hclosed hg₀ hmax hne)
    have huniform :
        |B.edgeContribution g₀ c W| ≤ τ := by
      exact B.abs_edgeContribution_le_of_frozen
        g₀ c W
        (hfrozen K B hclosed hg₀ hmax hne)
    rw [hcount, herase]
    calc
      |p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W -
          p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A))| =
          |B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W| := by
        congr 1
        ring
      _ ≤
          |B.edgeContribution g₀ b W| +
            |B.edgeContribution g₀ c W| :=
        abs_add_le _ _
      _ ≤
          Real.sqrt
              ((β g₀.card *
                  (B.strictBoundary g₀).bundleCount
                    ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) *
                ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                    (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) +
            τ :=
        add_le_add hdefect huniform
  · have hg₀empty : g₀ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    subst g₀
    let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    have hweight :
        ∀ y, W ∅ y = 1 := by
      intro y
      dsimp only [W]
      rw [B.pullbackBaseEdgeWeight_of_mem
        (orderedConfigurationBaseWeight A) hg₀ y]
      simp only [Finset.image_empty]
      exact orderedConfigurationBaseWeight_empty A
        (B.projectedEdgeTuple hg₀ y)
    have hcount :
        B.bundleCount W =
          (B.eraseEdge ∅).bundleCount
            ((B.eraseEdge ∅).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      calc
        B.bundleCount W =
            B.edgeContribution ∅ (W ∅) W :=
          B.bundleCount_eq_edgeContribution W hg₀
        _ =
            B.edgeContribution ∅ (fun _ => 1) W := by
          apply congrArg
            (fun q => B.edgeContribution ∅ q W)
          funext y
          exact hweight y
        _ = (B.eraseEdge ∅).bundleCount W := by
          rw [B.edgeContribution_const]
          simp
        _ =
            (B.eraseEdge ∅).bundleCount
              ((B.eraseEdge ∅).pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A)) :=
          B.eraseEdge_bundleCount_pullback ∅
            (orderedConfigurationBaseWeight A)
    rw [hcount, Finset.image_empty,
      orderedConfigurationBaseDensity_empty,
      one_mul, sub_self, abs_zero]
    exact add_nonneg (Real.sqrt_nonneg _) hτ
