-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.certificate_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:44:18.255067+00:00
-- url     : https://prove2.me/submissions/6438a12a-6dff-4607-8512-e750f6667e2d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_AdaptiveCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_GrowthFunctionRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_TowerDominatingGrowth
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_AdaptiveCoarseTargetSchedule_Landing_tolerance_nonneg
import Theorems.Thm_Wikipedia_SzemeredisTheorem_AdaptiveCoarseTargetSchedule_Realization_nonempty

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
# Adaptive top-down coarse-target regularity

The fixed-vector coarse-target theorem chooses one tower index at every
rank, but fixes all tower lengths before any of those choices are known.
For the removal argument this is unnecessarily rigid: after the top-rank
index has been selected, the horizon at the next rank may be chosen as a
function of that index, and so on.

This file packages such data as a finite decision tree.  A node contains
the tolerance, budget, and horizon for the current (highest remaining)
rank, together with one subtree for every admissible index.  Thus a branch
is genuinely path dependent.  A landing is a root-to-leaf branch.  Its
data are flattened in the bottom-up rank order used by
`CoarseTargetOrderedComplexRegularityCertificate`.
-/

namespace Wikipedia.SzemeredisTheorem



namespace AdaptiveCoarseTargetSchedule





namespace Landing

































end Landing





/-- Explicit existential form of adaptive coarse-target regularity.

This is the principal conversion endpoint for downstream arguments: it
returns an ordinary certificate, so all existing counting and cleaning
lemmas apply unchanged, while the equality identifies its index vector
with the realized decision-tree branch. -/
theorem exists_landing_certificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r)
    (hS : S.IsAdmissible) :
    ∃ P : S.Landing,
      ∃ R :
          CoarseTargetOrderedComplexRegularityCertificate
            G k r initial P.tolerance P.budget P.length,
        R.index = P.index := by
  obtain ⟨realization⟩ :=
    Realization.nonempty initial S hS
  exact
    ⟨realization.landing, realization.certificate,
      realization.index_eq⟩

end AdaptiveCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Source-style full coarse-target regularity

Tao's full regularity lemma does not choose the parameters at the different
ranks independently.  It first fixes a lower scale and then descends through
the ranks with a sufficiently fast auxiliary growth function.  The selected
scales have the shape

```
scaleFloor ≤ M_r,
F(M_{j + 1}) ≤ M_j,
gap_j ≤ 1 / F(M_{j + 1})^2,
regularity_j ≤ 1 / F(M_0).
```

This file isolates the exact adaptive certificate needed for that induction.
A `SourceFullCoarseTargetSchedule` is a finite top-down decision tree together
with numerical scale data on its genuine landings.  Its hypotheses are all
finite and ambient-independent.  The main compiler realizes the tree by
`AdaptiveCoarseTargetSchedule.exists_landing_certificate` and returns an
ordinary `CoarseTargetOrderedComplexRegularityCertificate` carrying the
source-style scale hierarchy.

The rank-zero plan and a genuine successor constructor are proved below.
The successor constructor makes the remaining mathematical obligation
explicit: after the current top index is selected, the lower plan must have
been built with scale floor `F(topScale)`, and the already fixed top
tolerance must be bounded by the common reciprocal attached to every landing
of that lower plan.  Constructing these lower plans uniformly is precisely
the auxiliary faster-growth induction in the source proof.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Source numerical targets -/









/-! ## Numerical bounds selected by an adaptive landing -/



/-! ## Adaptive source-full plans -/



namespace SourceFullCoarseTargetSchedule

/-- The scale hierarchy is antitone: deeper scales are no larger than
shallower scales. -/
theorem scale_antitone
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing) :
    Antitone (S.scale P) := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (S.scale P j.succ)).trans
        (S.scale_hierarchy P j))

/-- The fixed scale floor lies below every selected scale, not only the
deepest one. -/
theorem scaleFloor_le
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing)
    (q : Fin (r + 1)) :
    scaleFloor ≤ S.scale P q := by
  exact (S.scaleFloor_le_deepest P).trans
    (S.scale_antitone P (Fin.le_last q))

/-! ## Realized source-full certificates -/





/-! ## Rank-zero plan -/





/-! ## A genuine top-down successor constructor -/















/-! ## The finite faster-growth induction -/



namespace Bounded



end Bounded



































end SourceFullCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem

end
/-!
# Ambient-independent source-full bundle-removal parameters

This file packages two pieces of the final numerical diagonal.

* `sourceBundleDensity δ m = δ / (m + 1)` pays for a coarse upper
  partition of complexity at most `m` without choosing a global complexity
  window.
* `sourceBundleDefectScale δ η N m = η * sourceBundleDensity δ m ^ N`
  is small relative to every density power up to the fixed finite bundle
  horizon `N`.

The polynomial growth function

```
F(m) = Q * (m + 1)^N + (m + 1)
```

then makes both the common preliminary-regularity tolerance and the
rankwise source energy gaps small at the *same selected scale*.  This is the
pointwise choice which removes the apparent global complexity fixed point.

The last section retains the uniform ceiling supplied by
`SourceFullCoarseTargetSchedule.Bounded` when realizing the numerical plan
over an ambient finite type.  The older `certificate_nonempty` theorem
forgets the landing and hence cannot expose this ceiling to the uniform
count threshold.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Scale-dependent density and defect parameters -/
/-! ## Rankwise schedules attached to a selected scale hierarchy -/
/-! ## Polynomial pointwise growth -/
/-! ## Finite-horizon normalized counting bounds -/
/-! ## A bounded realized certificate -/
open Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded

open Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded in
/-- Realize a bounded numerical plan while retaining its landing-independent
ceiling. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty (Certificate S initial) := by
  obtain ⟨P, R, hindex⟩ :=
    S.plan.schedule.exists_landing_certificate
      initial S.plan.schedule_admissible
  let C : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor :=
    { tolerance := P.tolerance
      budget := P.budget
      length := P.length
      regularity := R
      scale := S.plan.scale P
      scaleFloor_le := S.plan.scaleFloor_le P
      scale_hierarchy := S.plan.scale_hierarchy P
      selected_tolerance_nonneg := by
        intro j
        simp only [selectedOrderedComplexTolerance]
        rw [congrFun hindex j]
        exact
          P.tolerance_nonneg S.plan.schedule_admissible
            j (P.index j)
      selected_tolerance_le_common := by
        intro j
        simpa [selectedOrderedComplexTolerance, hindex] using
          S.plan.selected_tolerance_le_common P j
      rank_gap_le := by
        intro j
        have hgap := R.gap_le j
        have hreciprocal := S.plan.reciprocal_gap_le P j
        change
          orderedLayerAtomEnergy
                (R.fine.partition j.castSucc)
                (R.coarse.partition j.succ) -
              orderedLayerAtomEnergy
                (R.coarse.partition j.castSucc)
                (R.coarse.partition j.succ) ≤
            sourceFullRankGap F (S.plan.scale P) j
        exact hgap.trans hreciprocal
      coarse_complexity := by
        intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            have htop := congrFun R.coarse_topLayer_eq e
            simp only [OrderedPartitionComplex.topLayer] at htop
            rw [htop]
            calc
              FacePartition.complexity
                    (initial.partition (Fin.last r) e) ≤
                  initialBound (Fin.last r) :=
                hinitial (Fin.last r) e
              _ = adaptiveSelectedCoarseLayerBound
                    initialBound P (Fin.last r) := by
                simp [adaptiveSelectedCoarseLayerBound]
              _ ≤ S.plan.scale P (Fin.last r) :=
                S.plan.selected_coarse_bound P (Fin.last r)
        | cast j =>
            intro e
            calc
              FacePartition.complexity
                    (R.coarse.partition j.castSucc e) ≤
                  fixedUpperLayerComplexityFactor
                        j.1 (P.budget j) (P.index j) *
                    FacePartition.complexity
                        (initial.partition j.castSucc e) := by
                rw [← congrFun hindex j]
                exact R.coarse_complexity j e
              _ ≤ fixedUpperLayerComplexityFactor
                        j.1 (P.budget j) (P.index j) *
                    initialBound j.castSucc :=
                Nat.mul_le_mul_left _ (hinitial j.castSucc e)
              _ = adaptiveSelectedCoarseLayerBound
                    initialBound P j.castSucc := by
                simp [adaptiveSelectedCoarseLayerBound]
              _ ≤ S.plan.scale P j.castSucc :=
                S.plan.selected_coarse_bound P j.castSucc }
  exact ⟨⟨C, S.scale_zero_le P⟩⟩
