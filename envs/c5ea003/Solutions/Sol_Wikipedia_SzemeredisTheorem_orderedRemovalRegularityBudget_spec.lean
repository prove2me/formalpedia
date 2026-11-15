-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.orderedRemovalRegularityBudget_spec
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:26:26.590807+00:00
-- url     : https://prove2.me/submissions/646f60f0-5522-4e5c-badb-632a2e5ad038

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Quantitative parameters for ordered hypergraph removal

This file contains only the numerical layer of ordered removal.  Semantic
cover and contradiction arguments live elsewhere.

For a removal allowance `ξ > 0` and a uniform bound `M` on every selected
fine partition, write `S` for the number of positive subfaces of one top
face and `N` for the number of positive faces in the whole ordered
configuration.  We choose

```
ρ = min (1 / 2) (ξ / (4 * (S * M + 1))),
θ = ρ ^ N / (4 * (N + 1)),
α = ρ,   δ = η = θ,   β = θ²,
γ = ξ * β / 4.
```

Then the sharp cleaning error is at most

```
S * M * α + γ / β ≤ ξ / 2 < ξ,
```

whereas the configuration-count lower bound is strictly positive because

```
N * (η + δ) < ρ ^ N.
```

The final sections give ambient-independent ceiling schedules for weak
regularity and frozen-upper energy selection, derive a uniform complexity
bound from `StrongOrderedComplexRegularityCertificate`, and state bridge
theorems.  The bridge makes the remaining diagonal compatibility
transparent: the selected regularity tolerance must be at most `θ`, and
the reciprocal-timescale energy budget must be at most `γ`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Face counts and explicit thresholds -/
/-! ## Arithmetic margins -/
/-! ## Ambient-independent ceiling schedules -/

open Wikipedia.SzemeredisTheorem in
/-- The ceiling construction satisfies the strict energy-length
hypothesis of one fixed-upper preliminary regularity pass. -/
theorem solution
    {k j : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
      (orderedRemovalRegularityBudget k j τ : ℝ) * τ ^ 2 := by
  have hsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hquot :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
          τ ^ 2 <
        (orderedRemovalRegularityBudget k j τ : ℝ) := by
    unfold orderedRemovalRegularityBudget
    calc
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
            τ ^ 2 ≤
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
              ((Fintype.card
                (OrderedFace k (j + 1)) : ℝ) /
                  τ ^ 2) + 1 : ℕ) : ℝ) := by
        norm_num
  exact (div_lt_iff₀ hsq).1 hquot
