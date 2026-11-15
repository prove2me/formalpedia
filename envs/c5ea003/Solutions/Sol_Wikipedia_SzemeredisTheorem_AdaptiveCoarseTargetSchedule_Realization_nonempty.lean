-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Realization.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:42:18.080196+00:00
-- url     : https://prove2.me/submissions/600e622d-443d-4530-b673-0f4453911d24

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_AdaptiveCoarseTargetSchedule_Landing_index_lt_length
import Theorems.Thm_Wikipedia_SzemeredisTheorem_OrderedPartitionComplex_appendTop_refines

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
# Shared ordered-face partitions and boundary pullbacks

The hypergraph-complex regularity proof uses one genuine partition on every
ordered lower face.  If `e` is an upper face, its boundary partition is not
an independently generated partition of the whole upper tuple space.  It is
the common refinement of the pullbacks of the shared partitions on the
immediate subfaces `eraseOrderedFace e i`.

This file implements that architecture.  Its central membership theorem says
that two upper tuples lie in the same boundary atom exactly when every pair
of erased tuples lies in the same atom of the corresponding genuine lower
face partition.  This is the compatibility needed for closed atom
configurations and localized energy estimates.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators











namespace OrderedFacePartitionRefines





end OrderedFacePartitionRefines





































namespace OrderedPartitionComplex









theorem Refines.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C D E : OrderedPartitionComplex G k r}
    (hCD : C.Refines D) (hDE : D.Refines E) :
    C.Refines E :=
  fun j e => le_trans (hCD j e) (hDE j e)



end OrderedPartitionComplex

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
theorem topLayer_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).topLayer = top := by
  simp [topLayer, appendTop]



@[simp]
theorem topLayer_withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    (withTopLayer C top).topLayer = top := by
  simp [topLayer, withTopLayer]



@[simp]
theorem appendTop_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (appendTop C top).partition j.castSucc =
      C.partition j := by
  simp [appendTop]

@[simp]
theorem appendTop_partition_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).partition (Fin.last (r + 1)) =
      top := by
  simp [appendTop]



@[simp]
theorem appendTop_dropTop_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    appendTop C.dropTop C.topLayer = C := by
  cases C with
  | mk partition =>
      simp only [dropTop, topLayer, appendTop]
      congr 1
      funext j e
      cases j using Fin.lastCases <;>
        simp only [Fin.lastCases_last,
          Fin.lastCases_castSucc]





/-- Replacing the top layer by a refinement refines the original complex
and leaves every lower layer unchanged. -/
theorem withTopLayer_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (htop : OrderedFacePartitionRefines top C.topLayer) :
    (withTopLayer C top).Refines C := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [withTopLayer, Fin.lastCases_last]
      change OrderedFace k r at e
      change top e ≤ C.partition (Fin.last r) e
      exact htop e
  | cast i =>
      simp only [withTopLayer, Fin.lastCases_castSucc]
      exact le_rfl

end OrderedPartitionComplex

/-! ## Coarse/fine complexes and honest atom-energy gaps -/



namespace OrderedCoarseFineComplex



























end OrderedCoarseFineComplex

/-! ## Rank schedules and simultaneous preliminary regularity -/













/-! ## The top-down all-rank construction -/







end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule

open Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Realization in
/-- Every admissible adaptive schedule has a genuine top-down realization.

The proof is a downward rank induction.  At the current top rank it runs
the fixed-upper adjacent-energy selector, uses the selected index to enter
the corresponding subtree, and only then constructs the lower-rank
certificate.  The concluding equality of index vectors rules out the
spurious interpretation in which a branch is chosen independently of the
regularity certificate. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r)
    (hS : S.IsAdmissible) :
    Nonempty (Realization k r initial S) := by
  induction r with
  | zero =>
      cases S with
      | nil =>
          let landing :
              (AdaptiveCoarseTargetSchedule.nil :
                AdaptiveCoarseTargetSchedule k 0).Landing :=
            Landing.nil
          let certificate :
              CoarseTargetOrderedComplexRegularityCertificate
                G k 0 initial
                  landing.tolerance landing.budget landing.length := {
            index := landing.index
            coarse := initial
            fine := initial
            refines :=
              OrderedPartitionComplex.Refines.refl initial
            coarse_refines_initial :=
              OrderedPartitionComplex.Refines.refl initial
            coarse_topLayer_eq := rfl
            fine_topLayer_eq := rfl
            index_lt := fun j => Fin.elim0 j
            mixedRegular := fun j => Fin.elim0 j
            gap_nonneg := fun j => Fin.elim0 j
            gap_le := fun j => Fin.elim0 j
            coarse_complexity := fun j => Fin.elim0 j
            fine_complexity := fun j => Fin.elim0 j }
          exact ⟨{
            landing := landing
            certificate := certificate
            index_eq := rfl }⟩
  | succ r ih =>
      cases S with
      | @node _ tolerance budget length next =>
          rcases hS with
            ⟨htolerance, hbudget, hlength, hnext⟩
          let lowerInitial :
              OrderedFacePartitionSystem G k r :=
            initial.dropTop.topLayer
          let upper :
              OrderedFacePartitionSystem G k (r + 1) :=
            initial.topLayer
          let topChoice :=
            chosenFixedUpperLayerCoarseFine
              lowerInitial upper tolerance budget
              htolerance hbudget length hlength
          let chosen : Fin length :=
            ⟨topChoice.index, topChoice.index_lt⟩
          let prepared :
              OrderedPartitionComplex G k r :=
            initial.dropTop.withTopLayer topChoice.coarse
          obtain ⟨lowerRealization⟩ :=
            ih prepared (next chosen) (hnext chosen)
          let lowerLanding := lowerRealization.landing
          let lowerCertificate := lowerRealization.certificate
          have hindexLower :
              lowerCertificate.index = lowerLanding.index :=
            lowerRealization.index_eq
          let landing :
              (AdaptiveCoarseTargetSchedule.node
                tolerance budget length next).Landing :=
            Landing.node
              (tolerance := tolerance) (budget := budget)
              chosen lowerLanding
          let coarsePrefix :
              OrderedPartitionComplex G k r :=
            lowerCertificate.coarse
          let finePrefix :
              OrderedPartitionComplex G k r :=
            lowerCertificate.fine.withTopLayer topChoice.fine
          let coarse :
              OrderedPartitionComplex G k (r + 1) :=
            coarsePrefix.appendTop upper
          let fine :
              OrderedPartitionComplex G k (r + 1) :=
            finePrefix.appendTop upper
          have hlowerFineTop :
              lowerCertificate.fine.topLayer =
                topChoice.coarse := by
            calc
              lowerCertificate.fine.topLayer =
                  prepared.topLayer :=
                lowerCertificate.fine_topLayer_eq
              _ = topChoice.coarse :=
                OrderedPartitionComplex.topLayer_withTopLayer
                  initial.dropTop topChoice.coarse
          have hlowerCoarseTop :
              lowerCertificate.coarse.topLayer =
                topChoice.coarse := by
            calc
              lowerCertificate.coarse.topLayer =
                  prepared.topLayer :=
                lowerCertificate.coarse_topLayer_eq
              _ = topChoice.coarse :=
                OrderedPartitionComplex.topLayer_withTopLayer
                  initial.dropTop topChoice.coarse
          let certificate :
              CoarseTargetOrderedComplexRegularityCertificate
                G k (r + 1) initial
                  landing.tolerance landing.budget landing.length := {
            index := landing.index
            coarse := coarse
            fine := fine
            refines := by
              have hprefix :
                  finePrefix.Refines coarsePrefix := by
                intro q e
                cases q using Fin.lastCases with
                | last =>
                    simp only [finePrefix, coarsePrefix,
                      OrderedPartitionComplex.withTopLayer,
                      Fin.lastCases_last]
                    change OrderedFace k r at e
                    have heq :
                        lowerCertificate.coarse.partition
                            (Fin.last r) e =
                          topChoice.coarse e :=
                      congrFun hlowerCoarseTop e
                    rw [heq]
                    exact topChoice.refines e
                | cast i =>
                    simp only [finePrefix, coarsePrefix,
                      OrderedPartitionComplex.withTopLayer,
                      Fin.lastCases_castSucc]
                    exact lowerCertificate.refines
                      i.castSucc e
              exact OrderedPartitionComplex.appendTop_refines
                hprefix
                (OrderedFacePartitionRefines.refl upper)
            coarse_refines_initial := by
              have hprepared :
                  prepared.Refines initial.dropTop := by
                exact
                  OrderedPartitionComplex.withTopLayer_refines
                    initial.dropTop topChoice.coarse
                    (by
                      simpa only [lowerInitial] using
                        topChoice.coarse_refines_initial)
              have hprefix :
                  coarsePrefix.Refines initial.dropTop :=
                OrderedPartitionComplex.Refines.trans
                  lowerCertificate.coarse_refines_initial
                  hprepared
              have happend :=
                OrderedPartitionComplex.appendTop_refines
                  hprefix
                  (OrderedFacePartitionRefines.refl upper)
              simpa [coarse, coarsePrefix, upper] using happend
            coarse_topLayer_eq := by
              simp [coarse, upper]
            fine_topLayer_eq := by
              simp [fine, upper]
            index_lt := by
              exact landing.index_lt_length
            mixedRegular := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    IsPreliminaryOrderedRegular
                      topChoice.fine upper
                      (landing.tolerance (Fin.last r)
                        (landing.index (Fin.last r)))
                  simpa [landing, chosen] using
                    topChoice.fine_regular
              | cast i =>
                  have hregular :=
                    lowerCertificate.mixedRegular i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    @IsPreliminaryOrderedRegular
                      G _ _ k i.1
                      (lowerCertificate.fine.partition
                        i.castSucc)
                      (lowerCertificate.coarse.partition
                        i.succ)
                      (landing.tolerance i.castSucc
                        (landing.index i.castSucc))
                  rw [show landing.tolerance i.castSucc =
                      lowerLanding.tolerance i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  exact hregular
            gap_nonneg := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  have hgap := topChoice.gap_nonneg
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    0 ≤
                      orderedLayerAtomEnergy
                          topChoice.fine upper -
                        orderedLayerAtomEnergy
                          lowerCertificate.coarse.topLayer
                          upper
                  rw [hlowerCoarseTop]
                  exact hgap
              | cast i =>
                  have hgap :=
                    lowerCertificate.gap_nonneg i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  convert hgap using 1
            gap_le := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  have hgap := topChoice.gap_le
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    orderedLayerAtomEnergy
                          topChoice.fine upper -
                        orderedLayerAtomEnergy
                          lowerCertificate.coarse.topLayer
                          upper ≤
                      (Fintype.card
                        (OrderedFace k (r + 1)) : ℝ) /
                          (landing.length (Fin.last r) : ℝ)
                  rw [hlowerCoarseTop]
                  simpa [landing] using hgap
              | cast i =>
                  have hgap :=
                    lowerCertificate.gap_le i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    orderedLayerAtomEnergy
                          (lowerCertificate.fine.partition
                            i.castSucc)
                          (lowerCertificate.coarse.partition
                            i.succ) -
                        orderedLayerAtomEnergy
                          (lowerCertificate.coarse.partition
                            i.castSucc)
                          (lowerCertificate.coarse.partition
                            i.succ) ≤
                      (Fintype.card
                        (OrderedFace k (i.1 + 1)) : ℝ) /
                          (landing.length i.castSucc : ℝ)
                  rw [show landing.length i.castSucc =
                      lowerLanding.length i by
                        simp [landing]]
                  exact hgap
            coarse_complexity := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change OrderedFace k r at e
                  have hcomplexity :=
                    topChoice.coarse_complexity e
                  simp only [coarse, coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.coarse.partition
                          (Fin.last r) e) ≤
                      fixedUpperLayerComplexityFactor
                          r (landing.budget (Fin.last r))
                          (landing.index (Fin.last r)) *
                        FacePartition.complexity
                          (initial.partition
                            (Fin.last r).castSucc e)
                  have heq :
                      lowerCertificate.coarse.partition
                          (Fin.last r) e =
                        topChoice.coarse e :=
                    congrFun hlowerCoarseTop e
                  rw [heq]
                  simp only [landing, chosen,
                    Landing.budget_node_last,
                    Landing.index_node_last]
                  convert hcomplexity using 1
              | cast i =>
                  intro e
                  change OrderedFace k i.1 at e
                  have hcomplexity :=
                    lowerCertificate.coarse_complexity i e
                  simp only [coarse, coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.coarse.partition
                          i.castSucc e) ≤
                      fixedUpperLayerComplexityFactor
                          i.1 (landing.budget i.castSucc)
                          (landing.index i.castSucc) *
                        FacePartition.complexity
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show landing.budget i.castSucc =
                      lowerLanding.budget i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  simp only [prepared,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc,
                    OrderedPartitionComplex.dropTop] at hcomplexity
                  convert hcomplexity using 1
            fine_complexity := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change OrderedFace k r at e
                  have hcomplexity :=
                    topChoice.fine_complexity e
                  simp only [fine, finePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last]
                  change
                    FacePartition.complexity
                        (topChoice.fine e) ≤
                      fixedUpperLayerComplexityFactor
                          r (landing.budget (Fin.last r))
                          (landing.index (Fin.last r) + 1) *
                        FacePartition.complexity
                          (initial.partition
                            (Fin.last r).castSucc e)
                  simp only [landing, chosen,
                    Landing.budget_node_last,
                    Landing.index_node_last]
                  convert hcomplexity using 1
              | cast i =>
                  intro e
                  change OrderedFace k i.1 at e
                  have hcomplexity :=
                    lowerCertificate.fine_complexity i e
                  simp only [fine, finePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.fine.partition
                          i.castSucc e) ≤
                      fixedUpperLayerComplexityFactor
                          i.1 (landing.budget i.castSucc)
                          (landing.index i.castSucc + 1) *
                        FacePartition.complexity
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show landing.budget i.castSucc =
                      lowerLanding.budget i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  simp only [prepared,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc,
                    OrderedPartitionComplex.dropTop] at hcomplexity
                  convert hcomplexity using 1 }
          exact ⟨{
            landing := landing
            certificate := certificate
            index_eq := rfl }⟩
