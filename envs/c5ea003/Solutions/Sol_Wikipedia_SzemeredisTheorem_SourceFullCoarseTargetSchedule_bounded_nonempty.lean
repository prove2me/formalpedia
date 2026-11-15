-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.bounded_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:27:48.115195+00:00
-- url     : https://prove2.me/submissions/3c2616de-ba64-46fe-a092-9082f8a5d18c

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_le_finiteMaximum
import Theorems.Thm_Wikipedia_SzemeredisTheorem_orderedFace_card_div_growthRegularityLength_lt
import Theorems.Thm_Wikipedia_SzemeredisTheorem_orderedRemovalRegularityBudget_spec

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# One-rank growth-function regularity

This file packages the preliminary one-rank selector underlying the
growth-function form of hypergraph regularity.  For a natural-valued growth
function `F`, an initial complexity bound `M₀`, and a fixed upper layer, the
schedule is constructed triangularly:

```
M 0       = M₀,
τ n       = 1 / F (M n),
B n       = ⌈card (OrderedFace k (j + 1)) / (τ n)²⌉ + 1,
M (n + 1) = (2^(j+1))^(B n) * M n.
```

The existing fixed-upper tower then selects adjacent coarse and fine stages.
The fine stage is preliminarily regular with error exactly `τ i`; a
one-rank energy pigeonhole makes the coarse/fine gap at most any prescribed
positive `γ`.  All numerical schedules are ambient-independent.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Natural growth functions -/



namespace NatGrowthFunction



theorem monotone (F : NatGrowthFunction) :
    Monotone F :=
  F.monotone'

theorem positive (F : NatGrowthFunction) (n : ℕ) :
    0 < F n := by
  exact lt_of_lt_of_le (Nat.zero_lt_succ n)
    (F.above_diagonal n)



end NatGrowthFunction

/-! ## The triangular numerical schedule -/



















theorem growthRegularityStepTolerance_pos
    (F : NatGrowthFunction) (M : ℕ) :
    0 < growthRegularityStepTolerance F M := by
  unfold growthRegularityStepTolerance
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive M)













/-! ## A one-rank energy timescale -/



theorem growthRegularityLength_pos
    (k j : ℕ) (γ : ℝ) :
    0 < growthRegularityLength k j γ := by
  unfold growthRegularityLength
  omega



/-! ## Growth-function fixed-upper selection -/





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





/-! ## Realized source-full certificates -/





/-! ## Rank-zero plan -/





/-! ## A genuine top-down successor constructor -/















/-! ## The finite faster-growth induction -/



namespace Bounded



end Bounded

























@[simp]
theorem sourceFullStageNext_ceiling
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    (sourceFullStageNext
      initialBound F topScale lowerBuilder i).ceiling =
      (sourceFullStagePlan
        initialBound F topScale lowerBuilder i.1).ceiling :=
  rfl

theorem sourceFullStageTolerance_pos
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    0 <
      sourceFullStageTolerance
        initialBound F topScale lowerBuilder n := by
  exact growthRegularityStepTolerance_pos F
    (sourceFullStagePlan
      initialBound F topScale lowerBuilder n).ceiling







end SourceFullCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
/-! ## Source numerical targets -/
/-! ## Numerical bounds selected by an adaptive landing -/
/-! ## Adaptive source-full plans -/
open Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule
/-! ## Realized source-full certificates -/
/-! ## Rank-zero plan -/
/-! ## A genuine top-down successor constructor -/
/-! ## The finite faster-growth induction -/

open Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule in
/-- Strengthened source-full existence with a uniform upper bound on the
largest scale.  The proof is by rank induction.  Its successor step is a
finite recursion through the top energy horizon, so there is no fixed-point
assumption on `F`. -/
theorem solution
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Nonempty
      (Bounded k r initialBound F scaleFloor) := by
  induction r generalizing scaleFloor with
  | zero =>
      exact
        ⟨boundedZero
          k initialBound F scaleFloor⟩
  | succ r ih =>
      let topScale : ℕ :=
        max scaleFloor
          (initialBound (Fin.last (r + 1)))
      let gap : ℝ :=
        1 / (F topScale : ℝ) ^ 2
      let length : ℕ :=
        growthRegularityLength k r gap
      let lowerBuilder :
          (bound : Fin (r + 1) → ℕ) →
            Bounded k r bound F (F topScale) :=
        fun bound =>
          Classical.choice
            (ih bound (F topScale))
      let tolerance : ℕ → ℝ :=
        sourceFullStageTolerance
          initialBound F topScale lowerBuilder
      let budget : ℕ → ℕ :=
        sourceFullStageBudget
          initialBound F topScale lowerBuilder
      let next :
          (i : Fin length) →
            Bounded k r
              (lowerInitialBound initialBound budget i)
              F (F topScale) :=
        fun i =>
          sourceFullStageNext
            initialBound F topScale lowerBuilder i
      have hgap_pos : 0 < gap := by
        dsimp only [gap]
        exact one_div_pos.mpr
          (sq_pos_of_pos
            (by exact_mod_cast F.positive topScale))
      let plan :
          SourceFullCoarseTargetSchedule
            k (r + 1) initialBound F scaleFloor :=
        node topScale tolerance budget length
          (fun i => (next i).plan)
          (by
            intro n
            exact
              (sourceFullStageTolerance_pos
                initialBound F topScale lowerBuilder n).le)
          (by
            intro n
            change
              (Fintype.card
                  (OrderedFace k (r + 1)) : ℝ) <
                (sourceFullStageBudget
                    initialBound F topScale lowerBuilder n : ℝ) *
                  (sourceFullStageTolerance
                    initialBound F topScale lowerBuilder n) ^ 2
            exact
              orderedRemovalRegularityBudget_spec
                (sourceFullStageTolerance_pos
                  initialBound F topScale lowerBuilder n))
          (by
            exact growthRegularityLength_pos k r gap)
          (by
            exact le_max_left _ _)
          (by
            exact le_max_right _ _)
          (by
            intro i P
            have hscale :
                (next i).plan.scale P 0 ≤
                  (sourceFullStagePlan
                    initialBound F topScale
                      lowerBuilder i.1).ceiling := by
              exact
                ((next i).scale_zero_le P).trans_eq
                  (sourceFullStageNext_ceiling
                    initialBound F topScale
                      lowerBuilder i)
            change
              growthRegularityStepTolerance F
                    (sourceFullStagePlan
                      initialBound F topScale
                        lowerBuilder i.1).ceiling ≤
                sourceFullCommonTolerance F
                  ((next i).plan.scale P)
            unfold growthRegularityStepTolerance
              sourceFullCommonTolerance
            apply one_div_le_one_div_of_le
            · exact_mod_cast
                F.positive ((next i).plan.scale P 0)
            · exact_mod_cast F.monotone hscale)
          (by
            have hgap :=
              orderedFace_card_div_growthRegularityLength_lt
                (k := k) (j := r) hgap_pos
            exact hgap.le)
      let ceiling : ℕ :=
        finiteMaximum length
          (fun i => (next i).ceiling)
      refine ⟨{
        plan := plan
        ceiling := ceiling
        scale_zero_le := ?_ }⟩
      intro P
      cases P with
      | node chosen lower =>
          dsimp only [plan, ceiling, node]
          change
            nodeScale topScale
                (fun i => (next i).plan.scale)
                (AdaptiveCoarseTargetSchedule.Landing.node
                  chosen lower) 0 ≤
              finiteMaximum length
                (fun i => (next i).ceiling)
          rw [show
            (0 : Fin (r + 2)) =
              (0 : Fin (r + 1)).castSucc by rfl]
          rw [nodeScale_node_castSucc]
          exact
            ((next chosen).scale_zero_le lower).trans
              (le_finiteMaximum
                (fun i => (next i).ceiling) chosen)
