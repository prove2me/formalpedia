-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_indicator_inter_smallAverageBaseSupport_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:28:30.121205+00:00
-- url     : https://prove2.me/submissions/d7996f66-bc66-4ab0-a101-2672b44a2b02

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mem_smallAverageBaseSupport
import Theorems.Thm_Wikipedia_SzemeredisTheorem_partitionAtomUnion_indicator_measurable

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Canonical atoms and unions of genuine partition atoms -/
/-! ## Sublevel atoms and low-density charging -/

open Wikipedia.SzemeredisTheorem in
/-- The part of `A` lying above atoms of conditional `A`-density below
`α` has normalized mass at most `α`. -/
theorem solution
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P : FacePartition Ω) (A : Finset Ω)
    {α : ℝ} (hα : 0 ≤ α) :
    mean (finsetIndicator
      (A ∩ smallAverageBaseSupport P (finsetIndicator A) α)) ≤
      α := by
  rw [show
      finsetIndicator
          (A ∩ smallAverageBaseSupport P (finsetIndicator A) α) =
        fun x =>
          finsetIndicator A x *
            finsetIndicator
              (smallAverageBaseSupport
                P (finsetIndicator A) α) x by
    funext x
    by_cases hxA : x ∈ A <;>
      by_cases hxB :
        x ∈ smallAverageBaseSupport P (finsetIndicator A) α <;>
      simp [hxA, hxB]]
  rw [FaceRegularityState.mean_mul_eq_mean_conditionalMean_mul
    P (finsetIndicator A)
      (finsetIndicator
        (smallAverageBaseSupport P (finsetIndicator A) α))
      (partitionAtomUnion_indicator_measurable P
        (smallAverageBaseAtoms P (finsetIndicator A) α))]
  calc
    mean (fun x =>
        conditionalMean P (finsetIndicator A) x *
          finsetIndicator
            (smallAverageBaseSupport P
              (finsetIndicator A) α) x) ≤
        mean (fun _x : Ω => α) := by
      apply mean_mono
      intro x
      by_cases hx :
          x ∈ smallAverageBaseSupport P (finsetIndicator A) α
      · rw [finsetIndicator_of_mem hx, mul_one]
        exact
          (mem_smallAverageBaseSupport
            P (finsetIndicator A) α x).1 hx |>.le
      · rw [finsetIndicator_of_not_mem hx, mul_zero]
        exact hα
    _ = α := mean_const α
