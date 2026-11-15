-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:11:04.572828+00:00
-- url     : https://prove2.me/theorems/88b4d61d-8ef3-4f4c-bd41-ac1e6a1c194c
-- title:
--   Ambient-independent source-full adaptive regularity schedules
-- statement:
--   For a natural growth function $F$ and selected scales $(M_0,\ldots,M_r)$, the common tolerance is $1/F(M_0)$ and the rankwise energy-gap target at the next scale is $1/F(M_{j+1})^2$. The scale hierarchy requires $F(M_{j+1})\le M_j$.
--
--   A source-full schedule attaches scales to each genuine landing of an admissible adaptive schedule tree. It bounds the selected coarse complexities by those scales, controls every selected tolerance by the common tolerance, and makes each reciprocal horizon gap fit its rankwise target. A realized certificate retains the ordinary coarse/fine regularity data and these selected-scale guarantees.
--
--   The bounded version adds a landing-independent ceiling for the largest selected scale. The bundle supplies zero-rank and successor constructors, scale-vector and initial-bound transports, and the stagewise construction of lower plans, tolerances, budgets, and complexity factors. Each stage builds its lower plan from the already accumulated factor before choosing the current tolerance and budget, avoiding a circular dependence on that same stage's new complexity factor. The numerical plan is fixed independently of the ambient finite vertex type.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullCoarseTargetRegularity.lean#L40-L901

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_AdaptiveCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_TowerDominatingGrowth
import Lean
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- The single preliminary-regularity tolerance used to compare every
selected rank with the largest selected scale `M₀`. -/
noncomputable def sourceFullCommonTolerance
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ) : ℝ :=
  1 / (F (scale 0) : ℝ)

/-- The source energy-gap target at the lower boundary of a rank-`j + 1`
upper layer. -/
noncomputable def sourceFullRankGap
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ)
    (j : Fin r) : ℝ :=
  1 / (F (scale j.succ) : ℝ) ^ 2





/-! ## Numerical bounds selected by an adaptive landing -/

/-- The coarse-layer complexity bound supplied directly by an adaptive
landing and an initial layerwise bound.  The unchanged top layer keeps its
initial bound; a non-top layer uses the selected fixed-upper tower factor. -/
def adaptiveSelectedCoarseLayerBound
    {k r : ℕ}
    (initialBound : Fin (r + 1) → ℕ)
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      fixedUpperLayerComplexityFactor
          j.1 (P.budget j) (P.index j) *
        initialBound j.castSucc)

/-! ## Adaptive source-full plans -/

/-- Ambient-independent source-full numerical data on an adaptive
coarse-target schedule.

The scales may depend on the genuine landing.  No condition is imposed on a
Cartesian product of unrelated stage indices.  `scaleFloor` is fixed before
the ambient finite type and is forced below the deepest scale on every
landing. -/
structure SourceFullCoarseTargetSchedule
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  schedule : AdaptiveCoarseTargetSchedule k r
  schedule_admissible : schedule.IsAdmissible
  scale : schedule.Landing → Fin (r + 1) → ℕ
  scaleFloor_le_deepest :
    ∀ P, scaleFloor ≤ scale P (Fin.last r)
  scale_hierarchy :
    ∀ P (j : Fin r),
      F (scale P j.succ) ≤ scale P j.castSucc
  selected_tolerance_le_common :
    ∀ P (j : Fin r),
      P.tolerance j (P.index j) ≤
        sourceFullCommonTolerance F (scale P)
  reciprocal_gap_le :
    ∀ P (j : Fin r),
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (P.length j : ℝ) ≤
        sourceFullRankGap F (scale P) j
  selected_coarse_bound :
    ∀ P q,
      adaptiveSelectedCoarseLayerBound initialBound P q ≤
        scale P q

namespace SourceFullCoarseTargetSchedule





/-! ## Realized source-full certificates -/

/-- A realized coarse-target certificate with Tao's full-regularity scale
hierarchy.  The ordinary certificate retains all refinement and exact
mixed-regularity data; this wrapper records the common discrepancy, the
rankwise source gaps, and the selected coarse complexity scales. -/
structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  regularity :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length
  scale : Fin (r + 1) → ℕ
  scaleFloor_le : ∀ q, scaleFloor ≤ scale q
  scale_hierarchy :
    ∀ j : Fin r,
      F (scale j.succ) ≤ scale j.castSucc
  selected_tolerance_nonneg :
    ∀ j : Fin r,
      0 ≤
        selectedOrderedComplexTolerance
          tolerance regularity.index j
  selected_tolerance_le_common :
    ∀ j : Fin r,
      selectedOrderedComplexTolerance
          tolerance regularity.index j ≤
        sourceFullCommonTolerance F scale
  rank_gap_le :
    ∀ j : Fin r,
      regularity.toCoarseFine.coarseUpperLayerAtomEnergyGap j ≤
        sourceFullRankGap F scale j
  coarse_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (regularity.coarse.partition q e) ≤
        scale q



/-! ## Rank-zero plan -/

/-- Rank zero has no regularity choices.  The only selected scale is the
maximum of the requested scale floor and the initial top-layer bound. -/
def zero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    SourceFullCoarseTargetSchedule
      k 0 initialBound F scaleFloor where
  schedule := .nil
  schedule_admissible := trivial
  scale := fun _ _ =>
    max scaleFloor (initialBound 0)
  scaleFloor_le_deepest := by
    intro P
    exact le_max_left _ _
  scale_hierarchy := by
    intro P j
    exact Fin.elim0 j
  selected_tolerance_le_common := by
    intro P j
    exact Fin.elim0 j
  reciprocal_gap_le := by
    intro P j
    exact Fin.elim0 j
  selected_coarse_bound := by
    intro P q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    change initialBound 0 ≤
      max scaleFloor (initialBound 0)
    exact le_max_right _ _



/-! ## A genuine top-down successor constructor -/

/-- Prepend one deepest scale to the scale vector of a selected lower
landing.  Naming this dependent match separately gives downstream proofs a
stable simplification rule. -/
def nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (P :
      (AdaptiveCoarseTargetSchedule.node
        tolerance budget length next).Landing) :
    Fin (r + 2) → ℕ :=
  match P with
  | .node chosen lower =>
      Fin.lastCases topScale
        (lowerScale chosen lower)



@[simp]
theorem nodeScale_node_last
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        (Fin.last (r + 1)) =
      topScale := by
  simp [nodeScale]

@[simp]
theorem nodeScale_node_castSucc
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (q : Fin (r + 1)) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        q.castSucc =
      lowerScale chosen lower q := by
  simp [nodeScale]

@[simp]
theorem sourceFullCommonTolerance_nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    sourceFullCommonTolerance F
        (nodeScale (tolerance := tolerance) (budget := budget)
          topScale lowerScale
          (AdaptiveCoarseTargetSchedule.Landing.node
            (tolerance := tolerance) (budget := budget)
            chosen lower)) =
      sourceFullCommonTolerance F
        (lowerScale chosen lower) := by
  unfold sourceFullCommonTolerance
  rw [show
    (0 : Fin (r + 2)) =
      (0 : Fin (r + 1)).castSucc by rfl]
  rw [nodeScale_node_castSucc]

/-- Initial layer bounds seen by the lower subtree after the current
top-rank stage `i` has been selected.

The new lower top layer is the selected coarse layer, hence its bound is the
selected fixed-upper tower factor times the old rank-`r` input bound.  All
strictly lower input layers are unchanged. -/
def lowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (budget : ℕ → ℕ)
    {length : ℕ}
    (i : Fin length) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (fixedUpperLayerComplexityFactor r budget i.1 *
      initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

/-- Extend source-full lower plans by one new top rank.

`topScale` is the new deepest scale.  Once the top energy selector chooses
`i`, the construction enters `next i`; that lower plan starts at scale floor
`F(topScale)`, which proves the new hierarchy link.  The only genuinely
source-specific compatibility hypothesis is `htopTolerance`: the top
tolerance fixed at stage `i` must already be no larger than the common
reciprocal attached to every landing of the selected lower plan. -/
def node
    {k r : ℕ}
    {initialBound : Fin (r + 2) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (topScale : ℕ)
    (tolerance : ℕ → ℝ)
    (budget : ℕ → ℕ)
    (length : ℕ)
    (next :
      (i : Fin length) →
        SourceFullCoarseTargetSchedule
          k r (lowerInitialBound initialBound budget i)
            F (F topScale))
    (htolerance : ∀ n, 0 ≤ tolerance n)
    (hbudget :
      ∀ n,
        (Fintype.card
            (OrderedFace k (r + 1)) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2)
    (hlength : 0 < length)
    (hscaleFloor : scaleFloor ≤ topScale)
    (hinitialTop :
      initialBound (Fin.last (r + 1)) ≤ topScale)
    (htopTolerance :
      ∀ (i : Fin length)
          (P : (next i).schedule.Landing),
        tolerance i.1 ≤
          sourceFullCommonTolerance F ((next i).scale P))
    (htopGap :
      (Fintype.card
          (OrderedFace k (r + 1)) : ℝ) /
            (length : ℝ) ≤
        1 / (F topScale : ℝ) ^ 2) :
    SourceFullCoarseTargetSchedule
      k (r + 1) initialBound F scaleFloor where
  schedule :=
    .node tolerance budget length
      (fun i => (next i).schedule)
  schedule_admissible := by
    exact ⟨htolerance, hbudget, hlength,
      fun i => (next i).schedule_admissible⟩
  scale :=
    nodeScale topScale
      (fun i => (next i).scale)
  scaleFloor_le_deepest := by
    intro P
    cases P with
    | node chosen lower =>
        simpa only [nodeScale_node_last] using
          hscaleFloor
  scale_hierarchy := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [Fin.succ_last,
              nodeScale_node_last,
              nodeScale_node_castSucc] using
              (next chosen).scaleFloor_le_deepest lower
        | cast q =>
            simpa only [Fin.succ_castSucc,
              nodeScale_node_castSucc] using
              (next chosen).scale_hierarchy lower q
  selected_tolerance_le_common := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_last,
              AdaptiveCoarseTargetSchedule.Landing.index_node_last,
              sourceFullCommonTolerance_nodeScale] using
              htopTolerance chosen lower
        | cast q =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_castSucc,
              AdaptiveCoarseTargetSchedule.Landing.index_node_castSucc,
              sourceFullCommonTolerance_nodeScale] using
              (next chosen).selected_tolerance_le_common
                lower q
  reciprocal_gap_le := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_last,
              sourceFullRankGap, Fin.succ_last,
              nodeScale_node_last, Fin.val_last]
            convert htopGap using 1
        | cast q =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_castSucc,
              sourceFullRankGap, Fin.succ_castSucc,
              nodeScale_node_castSucc,
              Fin.val_castSucc]
            convert
              (next chosen).reciprocal_gap_le lower q using 1
  selected_coarse_bound := by
    intro P q
    cases P with
    | node chosen lower =>
        cases q using Fin.lastCases with
        | last =>
            simpa [adaptiveSelectedCoarseLayerBound,
              nodeScale_node_last] using
              hinitialTop
        | cast q =>
            cases q using Fin.lastCases with
            | last =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower (Fin.last r)
            | cast j =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower j.castSucc

/-! ## The finite faster-growth induction -/

/-- A source-full plan together with a landing-independent upper bound for
its largest selected scale.  The bound is auxiliary: it is used only while
constructing the tolerance at the preceding rank and is erased from the
public existence theorem. -/
structure Bounded
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  plan :
    SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor
  ceiling : ℕ
  scale_zero_le :
    ∀ P : plan.schedule.Landing,
      plan.scale P 0 ≤ ceiling

namespace Bounded

/-- Transport only the initial-bound index of a bounded plan.  Its
numerical ceiling is definitionally unchanged. -/
def castInitialBound
    {k r : ℕ}
    {initialBound newInitialBound :
      Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : Bounded k r initialBound F scaleFloor)
    (h : initialBound = newInitialBound) :
    Bounded k r newInitialBound F scaleFloor where
  plan := h ▸ S.plan
  ceiling := S.ceiling
  scale_zero_le := by
    subst newInitialBound
    exact S.scale_zero_le

end Bounded

/-- The bounded form of the rank-zero plan. -/
def boundedZero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Bounded k 0 initialBound F scaleFloor where
  plan := zero k initialBound F scaleFloor
  ceiling := max scaleFloor (initialBound 0)
  scale_zero_le := by
    intro P
    change
      max scaleFloor (initialBound 0) ≤
        max scaleFloor (initialBound 0)
    exact le_rfl

/-- The lower input bound when the already accumulated top-tower
complexity factor is `factor`. -/
def factorLowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (factor : ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (factor * initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

/-- The accumulated fixed-upper factor before stage `n`.

At stage `n`, the lower plan is first constructed from the factor already
accumulated at stages `< n`.  Its uniform ceiling then determines the
current reciprocal tolerance and hence the current budget.  That new budget
is used only in the factor for stage `n + 1`.  This one-stage shift is the
finite fast-growth device which removes the apparent circularity. -/
noncomputable def sourceFullStageFactor
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      let previous :=
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n
      let lower :=
        lowerBuilder
          (factorLowerInitialBound
            initialBound previous)
      let tolerance :=
        growthRegularityStepTolerance
          F lower.ceiling
      let budget :=
        orderedRemovalRegularityBudget
          k r tolerance
      (2 ^ (r + 1)) ^ budget * previous

/-- The lower input bound presented at top-tower stage `n`. -/
noncomputable def sourceFullStageBound
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Fin (r + 1) → ℕ :=
  factorLowerInitialBound initialBound
    (sourceFullStageFactor
      initialBound F topScale lowerBuilder n)

/-- The bounded lower plan selected before the current top-stage tolerance
and budget are fixed. -/
noncomputable def sourceFullStagePlan
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Bounded k r
      (sourceFullStageBound
        initialBound F topScale lowerBuilder n)
      F (F topScale) :=
  lowerBuilder
    (sourceFullStageBound
      initialBound F topScale lowerBuilder n)

/-- The current top-stage tolerance, chosen from the already constructed
lower plan's uniform scale ceiling. -/
noncomputable def sourceFullStageTolerance
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℝ :=
  growthRegularityStepTolerance F
    (sourceFullStagePlan
      initialBound F topScale lowerBuilder n).ceiling

/-- The ceiling budget corresponding to the current top-stage tolerance. -/
noncomputable def sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℕ :=
  orderedRemovalRegularityBudget k r
    (sourceFullStageTolerance
      initialBound F topScale lowerBuilder n)





/-- The explicitly accumulated stage factor is exactly the standard
fixed-upper tower factor for the recursively chosen budget stream. -/
theorem fixedUpperLayerComplexityFactor_sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ∀ n,
      fixedUpperLayerComplexityFactor r
          (sourceFullStageBudget
            initialBound F topScale lowerBuilder) n =
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            fixedUpperLayerComplexityFactor r
              (sourceFullStageBudget
                initialBound F topScale lowerBuilder) n =
          (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            sourceFullStageFactor
              initialBound F topScale lowerBuilder n
      rw [ih]

/-- Rewriting the accumulated factor identifies the lower input bound used
by the generic successor constructor with the one used to build stage
`i`.  This is the local prefix-invariance statement: the factor at `i`
depends only on budgets at stages `< i`. -/
theorem lowerInitialBound_sourceFullStageBudget
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i =
      sourceFullStageBound
        initialBound F topScale lowerBuilder i.1 := by
  funext q
  cases q using Fin.lastCases with
  | last =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound,
        fixedUpperLayerComplexityFactor_sourceFullStageBudget]
  | cast q =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound]

/-- The stage-`i` lower plan, transported to the syntactic initial-bound
family expected by `node`. -/
noncomputable def sourceFullStageNext
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    Bounded k r
      (lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i)
      F (F topScale) :=
  (sourceFullStagePlan
      initialBound F topScale lowerBuilder i.1).castInitialBound
    (lowerInitialBound_sourceFullStageBudget
      initialBound F topScale lowerBuilder i).symm











end SourceFullCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.ctorIdx,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.mk.inj,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.mk.injEq,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.noConfusionType,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Certificate.ctorIdx,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Certificate.mk.inj,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Certificate.mk.injEq,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Certificate.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Certificate.noConfusionType,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.ctorIdx,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.factorLowerInitialBound.eq_1,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.lowerInitialBound.eq_1,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.mk.inj,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.mk.injEq,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.noConfusionType,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.nodeScale.eq_1,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.nodeScale.match_1,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.sourceFullStageBound.eq_1,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.sourceFullStageFactor.match_1,
    `Wikipedia.SzemeredisTheorem.adaptiveSelectedCoarseLayerBound.eq_1,
    `Wikipedia.SzemeredisTheorem.sourceFullRankGap.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


