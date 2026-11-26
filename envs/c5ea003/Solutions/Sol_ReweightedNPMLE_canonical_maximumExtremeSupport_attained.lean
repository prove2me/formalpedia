-- Prove2me | solution 1 for ReweightedNPMLE.canonical_maximumExtremeSupport_attained
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:24.84662+00:00
-- url     : https://prove2.me/submissions/e2c98026-0da6-48fe-90ef-898fe0d217a6

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_exists_independentRepresentationEvent_of_mem_convexHull
import Theorems.Thm_ReweightedNPMLE_fullExtremeSupportEvent_eq_independentRepresentationEvent
import Theorems.Thm_ReweightedNPMLE_maximumIndependentSupport_mem_of_pos

-- Inline helpers preserved from ReweightedNPMLE.FittedRegularity.
section
/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

namespace ReweightedNPMLE



theorem fittedValueSelection_isMax {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) :
    IsMaxOn C (weightedLogLikelihood w)
      (fittedValueSelection C hCcompact hCnonempty hCpos w) :=
  Classical.choose_spec (exists_fittedValue_maximizer hCcompact hCnonempty hCpos w)







































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.ExtremeSupport.
section
/-!
# Maximum independent optimizer support

This file defines the maximum cardinality of independent full-support finite
representations of a fitted vector.  The fixed-cardinality representation
events are measurable because their parameter sets are locally closed in
second-countable locally compact spaces and hence sigma-compact.  Projection
preserves sigma-compactness.  The maximum is attained when positive, is at
most the ambient dimension, and satisfies the canonical support-sensitivity
Jacobian bound.  Its identification with extreme mixing-measure supports is
a separate optimizer-fiber statement.
-/

open Set Filter MeasureTheory Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE









theorem maximumIndependentSupport_le {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (w : Fin n → ℝ) :
    maximumIndependentSupport D vhat w ≤ n := by
  classical
  apply Finset.sup_le
  intro k hk
  split_ifs
  · exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  · exact Nat.zero_le n

theorem independentRepresentationEvent_size_le {n k : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ} (hw : w ∈ independentRepresentationEvent D vhat k) : k ≤ n := by
  obtain ⟨_, A, _, hlin, _⟩ := hw
  simpa using hlin.fintype_card_le_finrank

theorem le_maximumIndependentSupport_of_mem {n k : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ} (hw : w ∈ independentRepresentationEvent D vhat k) :
    k ≤ maximumIndependentSupport D vhat w := by
  classical
  have hk := independentRepresentationEvent_size_le D vhat hw
  have hh := Finset.le_sup (s := Finset.range (n + 1))
    (f := fun j ↦ if w ∈ independentRepresentationEvent D vhat j then j else 0)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  simpa [maximumIndependentSupport, hw] using hh







theorem independentRepresentationEvent_size_pos {n k : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ} (hw : w ∈ independentRepresentationEvent D vhat k) : 0 < k := by
  obtain ⟨_, A, _, _, p, hp, _, _⟩ := hw
  apply Nat.pos_of_ne_zero
  intro hk
  letI : IsEmpty (Fin k) := ⟨fun i ↦ Nat.not_lt_zero i.val (hk ▸ i.isLt)⟩
  have hh := hp.2
  simp at hh

theorem maximumIndependentSupport_pos_of_mem_convexHull
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hD : D ⊆ C)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvHull : fittedValueSelection C hCcompact hCnonempty hCpos w ∈ convexHull ℝ D) :
    0 < maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos) w := by
  obtain ⟨k, hk⟩ := exists_independentRepresentationEvent_of_mem_convexHull
    C hC hCcompact hCnonempty hCpos D hD w hw hvHull
  exact (independentRepresentationEvent_size_pos D _ hk).trans_le
    (le_maximumIndependentSupport_of_mem D _ hk)



end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.MeasureExtremeSupport.
section
/-!
# Maximum support of full probability-measure extreme optimizers

The statistic is defined directly from arbitrary probability measures, not
from finite representations. The full extreme-optimizer characterization
identifies each cardinality event with the independent representation event.
Consequently its supremum is a measurable, attained maximum bounded by `n`.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE





theorem maximumIndependentSupport_eq_sSup {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w : Fin n → ℝ) :
    maximumIndependentSupport D vhat w =
      sSup {k | w ∈ independentRepresentationEvent D vhat k} := by
  let S : Set ℕ := {k | w ∈ independentRepresentationEvent D vhat k}
  have hbounded : BddAbove S := ⟨n, fun k hk ↦ independentRepresentationEvent_size_le D vhat hk⟩
  apply le_antisymm
  · by_cases hpos : 0 < maximumIndependentSupport D vhat w
    · exact le_csSup hbounded (maximumIndependentSupport_mem_of_pos D vhat hpos)
    · have hz : maximumIndependentSupport D vhat w = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  · exact csSup_le' (fun k hk ↦ le_maximumIndependentSupport_of_mem D vhat hk)



theorem maximumExtremeSupport_eq_maximumIndependentSupport {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (w : Fin n → ℝ) :
    maximumExtremeSupport A vhat w = maximumIndependentSupport (range A) vhat w := by
  rw [maximumIndependentSupport_eq_sSup]
  unfold maximumExtremeSupport
  congr 1
  ext k
  change (w ∈ fullExtremeSupportEvent A vhat k) ↔
    (w ∈ independentRepresentationEvent (range A) vhat k)
  rw [fullExtremeSupportEvent_eq_independentRepresentationEvent A hA hC hCpos hAC vhat hvmax k]







end ReweightedNPMLE
end

/-!
# Maximum support of full probability-measure extreme optimizers

The statistic is defined directly from arbitrary probability measures, not
from finite representations. The full extreme-optimizer characterization
identifies each cardinality event with the independent representation event.
Consequently its supremum is a measurable, attained maximum bounded by `n`.
-/

open Set MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (hChull : C ⊆ convexHull ℝ (range A))
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n) :
    let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
    0 < maximumExtremeSupport A vhat w ∧ maximumExtremeSupport A vhat w ≤ n ∧
      ∃ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ ∧
        (μ : Measure Θ).support.ncard = maximumExtremeSupport A vhat w := by
  dsimp only
  let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
  have hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w) :=
    fun w _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos w
  have heq := maximumExtremeSupport_eq_maximumIndependentSupport A hA hC hCpos hAC vhat hvmax w
  have hpos := maximumIndependentSupport_pos_of_mem_convexHull C hC hCcompact hCnonempty
    hCpos (range A) hAC w hw (hChull (hvmax w hw).1)
  have hevent := maximumIndependentSupport_mem_of_pos (range A) vhat hpos
  rw [← fullExtremeSupportEvent_eq_independentRepresentationEvent A hA hC hCpos hAC
    vhat hvmax] at hevent
  rw [← heq] at hevent hpos
  exact ⟨hpos, heq.trans_le (maximumIndependentSupport_le (range A) vhat w), hevent.2⟩
