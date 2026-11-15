-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:48:42.341943+00:00
-- url     : https://prove2.me/submissions/6fad9705-0377-41c3-9511-26e1b77406ba

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedFullBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPatternPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullOrderedRemoval
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_ClosedOrderedAtomConfiguration_isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
import Theorems.Thm_Wikipedia_SzemeredisTheorem_partialConfigurationWeight_univ_eq_zero_of_not_occurrence

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
# Complete ordered partite hypergraph patterns

Recursive hypergraph removal naturally produces lower-rank constraints on a
fixed collection of vertex classes.  It is convenient to index an ordered
rank-`r` face by an embedding `Fin r ↪ Fin k`.  This permits composition of
faces without quotienting by permutations.

This file defines weighted and unweighted complete ordered patterns, their
normalized occurrence counts, deletions, and the uniform removal property
used by the rank induction.  Rank zero is proved directly.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

































namespace WeightedOrderedPattern











end WeightedOrderedPattern



namespace OrderedPattern





@[simp]
theorem mem_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) :
    x ∈ H.occurrenceFinset ↔ H.IsOccurrence x := by
  simp [occurrenceFinset]









/-- An occurrence has zero-one pattern weight one. -/
theorem toWeighted_patternWeight_of_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 1 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  apply Finset.prod_eq_one
  intro e _he
  simp [toWeighted, hx e]

/-- A nonoccurrence has zero-one pattern weight zero. -/
theorem toWeighted_patternWeight_of_not_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 0 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  obtain ⟨e, he⟩ := not_forall.mp hx
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  simp [toWeighted, he]













end OrderedPattern







end Wikipedia.SzemeredisTheorem

end

section



/-!
# Atom-family energy on shared ordered boundaries

Full hypergraph regularity simultaneously controls the indicators of every
atom in an upper-face partition.  Because those atoms are disjoint and
exhaust the tuple space, their aggregate conditional-expectation energy is
at most one.  This is substantially sharper than treating them as an
arbitrary family, whose naive energy budget is the number of targets.

This file first proves the generic finite-partition atom identities, then
specializes the energy to the shared ordered-boundary partitions from
`OrderedBoundaryPartition.lean`.  The final Pythagorean identity is the exact
coarse/fine defect budget used to show that most closed atom configurations
are good.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Indicators of genuine partition atoms -/







theorem partitionAtomIndicator_nonneg
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    0 ≤ partitionAtomIndicator Q a x := by
  by_cases hx : x ∈ a.1 <;> simp [hx]

theorem partitionAtomIndicator_le_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Q : FacePartition Ω) (a : Q.parts) (x : Ω) :
    partitionAtomIndicator Q a x ≤ 1 := by
  by_cases hx : x ∈ a.1 <;> simp [hx]



















/-! ## Ordered shared-boundary atom energy -/











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
# All-rank ordered preliminary regularity

The preliminary energy increment acts on one adjacent pair of ranks: it
refines the shared rank-`j` partitions while keeping rank `j + 1` fixed.
This file assembles those refinements into one compatible partition complex.
The ranks are processed from top to bottom.  Consequently, once the pair
`(j, j + 1)` has been regularized, later steps only change lower ranks and
cannot invalidate it.

The resulting theorem has a separate tolerance and finite energy budget at
every adjacent pair.  It returns an explicit stopping-time schedule, a
refining complex which is preliminarily regular at every rank, and the
ambient-independent complexity multiplier at every non-top layer.

We also package coarse/fine complexes and their boundary atom-energy gap.
The gap uses the atoms of the fine upper layer at both endpoints; with that
choice, refinement of the lower boundary gives honest monotonicity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedPartitionComplex













@[simp]
theorem topLayer_withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    (withTopLayer C top).topLayer = top := by
  simp [topLayer, withTopLayer]

















end OrderedPartitionComplex

/-! ## Coarse/fine complexes and honest atom-energy gaps -/



namespace OrderedCoarseFineComplex



























end OrderedCoarseFineComplex

/-! ## Rank schedules and simultaneous preliminary regularity -/













/-! ## The top-down all-rank construction -/







end Wikipedia.SzemeredisTheorem

end

section






/-!
# Positive counts for good closed ordered configurations

This file turns the local good-atom estimates into a direct positive-count
recurrence.  The edge index contains every positive-rank ordered face of an
ordered partition complex.  On downward-closed face families, the count is
the normalized mean of the selected atom indicators.  On other families we
use the exact product of the coarse densities; this total extension lets us
apply the finite abstract recurrence without asking localized estimates on
families which omit their boundary.

At a maximum-rank face, the remaining product contains every proper
boundary factor.  Thus it is supported on the canonical coarse boundary
atom.  The identity

```text
1_A = p + (E_fine 1_A - p) + (1_A - E_fine 1_A)
```

then gives the recurrence.  The uniform term is tested against a bounded
boundary product after freezing the outside variables.  The defect term is
bounded by localized Cauchy--Schwarz; the boundary support and unit bounds
make its square at most the good-atom defect threshold.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive-rank faces and immediate downward closure -/



namespace PositiveOrderedFace

















end PositiveOrderedFace











/-! ## Missing coordinates for lower-or-equal rank faces -/











/-! ## Selected atom weights and counts -/



theorem configurationFaceWeight_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ configurationFaceWeight A e y :=
  partitionAtomIndicator_nonneg _ _ _

theorem configurationFaceWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationFaceWeight A e y ≤ 1 :=
  partitionAtomIndicator_le_one _ _ _













theorem partialConfigurationWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) :
    partialConfigurationWeight A s x ≤ 1 := by
  unfold partialConfigurationWeight
  apply Finset.prod_le_one
  · intro e he
    exact configurationFaceWeight_nonneg A e _
  · intro e he
    exact configurationFaceWeight_le_one A e _

/-! ## Freezing and grouping a maximum-rank remainder -/













/-! ## Coarse densities, defects, and boundary support -/



























/-! ## Selected-face contributions and exact decomposition -/











/-! ## Uniform contribution -/





/-! ## Localized defect contribution -/















/-! ## The one-face recurrence -/













/-! ## Quantitative full-count lower bound and positivity -/





end Wikipedia.SzemeredisTheorem

end

section



/-!
# Ordered pattern edge partitions

The top layer used in ordered removal must remember the original
hypergraph.  For every top face we therefore generate a two-cell partition
from its edge set.  Any later refinement of that layer has atoms which are
monochromatic for the original edge predicate.

The lower layers of `orderedPatternInitialComplex` are indiscrete.  This is
the canonical starting complex for the all-rank regularity argument.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Edge supports and their two-cell partitions -/













/-! ## Canonical initial complex -/





@[simp]
theorem orderedPatternInitialComplex_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    (orderedPatternInitialComplex H).topLayer =
      orderedPatternTopPartition H := by
  exact OrderedPartitionComplex.topLayer_withTopLayer _ _

/-- Refining the initial complex in particular refines the original
edge/nonedge partition at the top rank. -/
theorem orderedPatternTopPartition_refines_of_complex_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : C.Refines (orderedPatternInitialComplex H)) :
    OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H) := by
  intro e
  change
    C.partition (Fin.last r) e ≤
      orderedPatternTopPartition H e
  rw [← orderedPatternInitialComplex_topLayer H]
  exact hC (Fin.last r) e

/-! ## Closed configurations contained in the original pattern -/





end Wikipedia.SzemeredisTheorem

end

section




/-!
# The ordered removal cover contradiction

This file joins the three semantic parts of ordered hypergraph removal.

* The top partition remembers the original edge predicates.
* A tuple surviving every bad-base deletion determines a good closed fine
  atom configuration.
* The configuration counting lemma gives every good configuration a
  uniform lower count.

Every tuple counted by the selected configuration remains an occurrence of
the original pattern, because its selected top atoms are edge-monochromatic.
Thus an occurrence surviving all deletions would force the original pattern
count above the assumed small-count threshold.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## The selected configuration lies inside the original pattern -/









/-- Pointwise, the indicator product for an occurring closed configuration
is bounded by the original zero-one pattern weight. -/
theorem partialConfigurationWeight_univ_le_patternWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    (x : Fin k → G) :
    partialConfigurationWeight A Finset.univ x ≤
      H.toWeighted.patternWeight x := by
  by_cases hx : H.IsOccurrence x
  · rw [H.toWeighted_patternWeight_of_occurrence hx]
    exact partialConfigurationWeight_le_one
      A Finset.univ x
  · rw [H.toWeighted_patternWeight_of_not_occurrence hx,
      partialConfigurationWeight_univ_eq_zero_of_not_occurrence
        H hC A hA hx]

/-- The normalized count of an occurring closed configuration is bounded
by the normalized count of the original pattern. -/
theorem fullConfigurationCount_le_patternCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness) :
    fullConfigurationCount A ≤
      H.toWeighted.patternCount := by
  unfold fullConfigurationCount partialConfigurationCount
    WeightedOrderedPattern.patternCount
  exact mean_mono
    (partialConfigurationWeight_univ_le_patternWeight
      H hC A hA)

/-! ## The cover contradiction -/





end Wikipedia.SzemeredisTheorem

end

section


/-!
# Full lower boundaries of ordered faces

The source hypergraph regularity argument conditions an upper face on the
join of the partitions carried by *all* of its nonempty proper subfaces.
The adjacent-rank boundary in `OrderedBoundaryPartition` is enough to encode
closedness, but it does not expose this source-level sigma algebra directly.

This file constructs that full lower boundary.  A proper positive subface of
an `n + 1` tuple is represented by a positive ordered face of that tuple
whose rank is at most `n`.  Each genuine partition in the ambient ordered
complex is pulled back to the selected upper tuple space, and the full lower
boundary is their finite common refinement.

The last section packages the coarse/fine defect and the corresponding
source mixed-goodness condition.  Its principal consequence is the localized
weighted square-defect estimate on the selected full-lower atom.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Proper positive subfaces -/





/-! ## The full lower partition -/







/-- Restricting through the ambient face agrees with first selecting the
upper tuple and then selecting its local proper subface. -/
@[simp]
theorem orderedFaceTuple_orderedFullLowerAmbientFace
    {G : Type*} {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1)
    (x : Fin k → G) :
    orderedFaceTuple (orderedFullLowerAmbientFace e d) x =
      orderedFaceTuple d.face (orderedFaceTuple e.face x) :=
  rfl























/-! ## Selected full-lower atoms and their weights -/





















/-! ## Source full-lower goodness -/























end Wikipedia.SzemeredisTheorem

end
/-!
# Source-full bad-base cleaning and the ordered removal contradiction

The source-full counting argument conditions the usual adjacent-boundary
square defect on the join of every proper lower face.  `SourceFullGoodAtoms`
shows that cleaning the resulting bad bases nevertheless costs only

```
upper complexity * density threshold + adjacent atom-energy gap / defect threshold.
```

This file pulls those bad bases back to top faces, records the corresponding
normalized deletion bounds, and proves the semantic cover contradiction.  A
tuple surviving every top-face deletion induces its canonical coarse closed
configuration; factorization of each positive face through a top face shows
that this configuration avoids every source-full bad base and is therefore
source-full mixed-good.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Surviving tuples are source-full mixed-good -/
/-! ## Abstract source-good cover contradiction -/

open Wikipedia.SzemeredisTheorem in
/-- A uniform lower count for every source-full mixed-good coarse
configuration forces the source-full bad-base family to cover every
occurrence of the original pattern. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ) (c : ℝ)
    (hcount : H.toWeighted.patternCount < c)
    (hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration
          G k (n + 1) P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A) :
    H.IsCover
      (P.sourceFullBadBaseDeletionFamily α β) := by
  intro x hx
  by_contra hsurvives
  push Not at hsurvives
  let A :
      ClosedOrderedAtomConfiguration
        G k (n + 1) P.coarse :=
    ClosedOrderedAtomConfiguration.ofTuple P.coarse x
  have hgood : A.IsSourceFullMixedGood P α β := by
    exact
      ClosedOrderedAtomConfiguration.isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
        hrk P x α β hsurvives
  have hcA : c ≤ fullConfigurationCount A :=
    hgoodCount A hgood
  have htop :
      OrderedFacePartitionRefines P.coarse.topLayer
        (orderedPatternTopPartition H) :=
    orderedPatternTopPartition_refines_of_complex_refines_initial
      H hinitial
  have hAH :
      fullConfigurationCount A ≤
        H.toWeighted.patternCount :=
    fullConfigurationCount_le_patternCount
      H htop A ((H.mem_occurrenceFinset x).1 hx)
  linarith
