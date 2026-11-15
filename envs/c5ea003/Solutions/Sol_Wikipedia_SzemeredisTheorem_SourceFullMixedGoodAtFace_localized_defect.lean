-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SourceFullMixedGoodAtFace.localized_defect
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:31:12.262797+00:00
-- url     : https://prove2.me/submissions/01cbf197-c404-43fc-8829-e996c6cb1730

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_mul_partitionAtomIndicator

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
# Finite face partitions

The finite regularity argument uses partitions of finite face spaces.  This
file fixes the refinement convention, packages common refinements and
partitions generated by cuts, and constructs pullbacks along maps of finite
types.

Mathlib orders `Finpartition` by refinement: `P ≤ Q` means that `P` is finer
than `Q`.  Consequently the lattice infimum is the common refinement.
-/

namespace Wikipedia.SzemeredisTheorem



namespace FacePartition

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]



















/-- The canonical representative belongs to its atom. -/
theorem representative_mem
    (P : FacePartition Ω) (a : P.parts) :
    P.representative a ∈ a.1 :=
  Classical.choose_spec (P.nonempty_of_mem_parts a.2)























/-! ## Finite common refinements -/





















































end FacePartition

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





















/-! ## Ordered shared-boundary atom energy -/











end Wikipedia.SzemeredisTheorem

end

section


/-!
# Good ordered atoms and localized bad-base accounting

The hypergraph removal argument must localize a global coarse--fine energy
gap to genuine boundary atoms.  This file supplies the finite bookkeeping
for that step.

For an arbitrary finite partition we define the union of a selected family
of atoms and prove that its normalized mass is the sum of the atom masses.
Sublevel atoms charge only a small part of a target atom, while atoms on
which a nonnegative local average is large satisfy a finite Markov bound.
Applying this to the square of a coarse--fine conditional-density defect
gives the headline estimate

```text
mass (upperAtom ∩ badBase) ≤
  densityThreshold + atomEnergyGap / defectThreshold.
```

The final section specializes these definitions to shared ordered
boundaries and packages realizable closed atom configurations.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Canonical atoms and unions of genuine partition atoms -/





























/-- Conditional control on one atom implies the equivalent localized
global-mass inequality. -/
theorem mean_mul_partitionAtomIndicator_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ) (a : P.parts)
    {β : ℝ}
    (hβ : conditionalMean P f (P.representative a) ≤ β) :
    mean (fun x => f x * partitionAtomIndicator P a x) ≤
      β * mean (partitionAtomIndicator P a) := by
  rw [mean_mul_partitionAtomIndicator P f a]
  apply mul_le_mul_of_nonneg_right hβ
  exact mean_nonneg fun x =>
    partitionAtomIndicator_nonneg P a x

/-! ## Sublevel atoms and low-density charging -/









/-! ## Large local averages and finite Markov bounds -/











/-! ## Coarse--fine defect bases -/

























/-! ## Ordered boundary specialization -/



























/-! ## Good local configurations and closed atom configurations -/









namespace ClosedOrderedAtomConfiguration













end ClosedOrderedAtomConfiguration

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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Proper positive subfaces -/
/-! ## The full lower partition -/
/-! ## Selected full-lower atoms and their weights -/
/-! ## Source full-lower goodness -/

/-- Pointwise source goodness yields the localized weighted-defect estimate
used in the source counting argument. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ)
    (hgood : SourceFullMixedGoodAtFace P A e α β) :
    sourceFullMixedLocalizedDefectSq P A e ≤
      β * mean (sourceFullMixedBoundaryWeight P A e) := by
  unfold sourceFullMixedLocalizedDefectSq
  apply mean_mul_partitionAtomIndicator_le
    (orderedFullLowerBoundaryPartition P.coarse e)
    (fun y => sourceFullMixedDefect P A e y ^ 2)
    (orderedFullLowerBoundaryAtomAt P.coarse e
      (orderedFaceTuple e.face A.witness))
  have hrep :
      (orderedFullLowerBoundaryPartition P.coarse e).representative
          (orderedFullLowerBoundaryAtomAt P.coarse e
            (orderedFaceTuple e.face A.witness)) ∈
        (orderedFullLowerBoundaryPartition P.coarse e).part
          (orderedFaceTuple e.face A.witness) := by
    exact
      (orderedFullLowerBoundaryPartition P.coarse e).representative_mem
        (orderedFullLowerBoundaryAtomAt P.coarse e
          (orderedFaceTuple e.face A.witness))
  have heq :=
    conditionalMean_eq_of_mem_part
      (orderedFullLowerBoundaryPartition P.coarse e)
      (fun y => sourceFullMixedDefect P A e y ^ 2)
      hrep
  rw [heq]
  exact hgood.2
