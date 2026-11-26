-- Prove2me | solution 1 for ReweightedNPMLE.effective_dimension_full_support
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:16:25.5246+00:00
-- url     : https://prove2.me/submissions/6d9cac0f-8316-4e26-a27e-2b2f5d2ce1bc

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
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
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedLocalization
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_FullEffectiveDimension
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_canonical_maximumExtremeSupport_attained
import Theorems.Thm_ReweightedNPMLE_coordinateLog_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_effective_dimension_finite_support
import Theorems.Thm_ReweightedNPMLE_exists_local_positive_weight_lower_bound
import Theorems.Thm_ReweightedNPMLE_exists_uniform_positive_coordinate_bounds
import Theorems.Thm_ReweightedNPMLE_fittedValue_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_fullExtremeSupportEvent_eq_independentRepresentationEvent
import Theorems.Thm_ReweightedNPMLE_full_extreme_optimizer_support_finite_card_le
import Theorems.Thm_ReweightedNPMLE_maximumIndependentSupport_mem_of_pos
import Theorems.Thm_ReweightedNPMLE_measurable_maximumIndependentSupport

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













/-- Quantitative local Lipschitz bound for the fitted log-vector. -/
theorem fittedLog_lipschitzOn {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {a c B : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ w ∈ s, ∀ i, a ≤ w i)
    (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hvB : ∀ w ∈ s, ∀ i, vhat w i ≤ B)
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    LipschitzOnWith
      ⟨((n : ℝ) * B ^ 2 / (a * c)) / c, by positivity⟩
      (fun w i ↦ Real.log (vhat w i)) s := by
  exact coordinateLog_lipschitzOn vhat hc hvc
    (fittedValue_lipschitzOn hC hCpos vhat ha hc hB hwa hvc hvB hmax)











theorem canonicalFittedLog_continuousAt
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    {w : Fin n → ℝ} (hw : w ∈ positiveVectors n) :
    ContinuousAt (fittedLogSelection C hCcompact hCnonempty hCpos) w := by
  obtain ⟨c, B, hc, hB, hbound⟩ := exists_uniform_positive_coordinate_bounds hCcompact hCpos
  obtain ⟨a, ha, s, hs, hwa⟩ := exists_local_positive_weight_lower_bound w hw
  have hlip := fittedLog_lipschitzOn (s := s) hC hCpos
    (fittedValueSelection C hCcompact hCnonempty hCpos) ha hc hB hwa
    (fun u _ i ↦ (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).1)
    (fun u _ i ↦ (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).2)
    (fun u _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos u)
  exact hlip.continuousOn.continuousAt hs

theorem canonicalFittedLog_continuousOn
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) :
    ContinuousOn (fittedLogSelection C hCcompact hCnonempty hCpos) (positiveVectors n) := by
  intro w hw
  exact (canonicalFittedLog_continuousAt C hC hCcompact hCnonempty hCpos hw).continuousWithinAt









theorem canonicalFittedValue_continuousOn
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) :
    ContinuousOn (fittedValueSelection C hCcompact hCnonempty hCpos) (positiveVectors n) := by
  apply continuousOn_pi.mpr
  intro i
  have hlog := (continuous_apply i).comp_continuousOn
    (canonicalFittedLog_continuousOn C hC hCcompact hCnonempty hCpos)
  apply (Real.continuous_exp.comp_continuousOn hlog).congr
  intro w hw
  exact (Real.exp_log (hCpos (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 i)).symm

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

theorem measurable_maximumExtremeSupport {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (hvcont : ContinuousOn vhat (positiveVectors n)) :
    Measurable (maximumExtremeSupport A vhat) := by
  have heq : maximumExtremeSupport A vhat = maximumIndependentSupport (range A) vhat :=
    funext (maximumExtremeSupport_eq_maximumIndependentSupport A hA hC hCpos hAC vhat hvmax)
  rw [heq]
  exact measurable_maximumIndependentSupport (range A) (isCompact_range hA).isClosed vhat hvcont

theorem full_extreme_optimizer_support_le_maximum {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (μ : ProbabilityMeasure Θ) (hext : IsExtremeProbabilityMixture A (vhat w) μ) :
    (μ : Measure Θ).support.Finite ∧
      (μ : Measure Θ).support.ncard ≤ maximumExtremeSupport A vhat w := by
  have hfinite := full_extreme_optimizer_support_finite_card_le A hA hC hCpos hAC
    w (vhat w) hw (hvmax w hw) μ hext
  have hevent : w ∈ fullExtremeSupportEvent A vhat (μ : Measure Θ).support.ncard :=
    ⟨hw, μ, hext, rfl⟩
  rw [fullExtremeSupportEvent_eq_independentRepresentationEvent A hA hC hCpos hAC
    vhat hvmax] at hevent
  rw [maximumExtremeSupport_eq_maximumIndependentSupport A hA hC hCpos hAC vhat hvmax w]
  exact ⟨hfinite.1, le_maximumIndependentSupport_of_mem (range A) vhat hevent⟩



end ReweightedNPMLE
end

/-!
# Effective-dimension sparsification for the full optimizer fiber

This is the abstract paper theorem for a continuous positive dictionary on a
nonempty compact metric space. Its support statistic ranges over all extreme
probability-measure optimizers. All near-optimal-fit conclusions hold on the
same measurable event, with explicit universal constants.
-/

open Set MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The full-measure form of the paper's effective-dimension theorem. The
constants are `C = 10000000` and `c = 1/3072`; no regularity, moment estimate,
or finiteness of extreme supports is assumed. -/
theorem solution
    {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {n r : ℕ} [Nonempty (Fin n)] {α q η : ℝ}
    (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hscale : 10000000 * ((r : ℝ) + effectiveQ n q) ≤ α)
    (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (A : Θ → Fin n → ℝ) (hA : Continuous A) (hApos : ∀ θ i, 0 < A θ i)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r)
    (hwidth : ∀ u ∈ relativeFittedSet (convexHull ℝ (range A))
      (fittedValueSelection (convexHull ℝ (range A))
        (positive_kernel_hull_properties A hA hApos).1
        (positive_kernel_hull_properties A hA hApos).2.1
        (positive_kernel_hull_properties A hA hApos).2.2 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    let C := convexHull ℝ (range A)
    let vhat := fittedValueSelection C (positive_kernel_hull_properties A hA hApos).1
      (positive_kernel_hull_properties A hA hApos).2.1
      (positive_kernel_hull_properties A hA hApos).2.2
    let v₀ := vhat 1
    Measurable (maximumExtremeSupport A vhat) ∧
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
        ∀ w ∈ G, (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
          w ∈ positiveVectors n ∧
          (maximumExtremeSupport A vhat w : ℝ) ≤ 10000000 * ((r : ℝ) + q) ∧
          (0 < maximumExtremeSupport A vhat w ∧ maximumExtremeSupport A vhat w ≤ n ∧
            ∃ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ ∧
              (μ : Measure Θ).support.ncard = maximumExtremeSupport A vhat w) ∧
          (∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
            (μ : Measure Θ).support.Finite ∧
              ((μ : Measure Θ).support.ncard : ℝ) ≤ 10000000 * ((r : ℝ) + q)) ∧
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ∧
          weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ≤
            10000000 * ((r : ℝ) + q) / α ∧
          (∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤ 10000000 * ((r : ℝ) + q) / α ∧
          ∀ (τ : ℝ), 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
            weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
            0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
            weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤
              10000000 * (((r : ℝ) + q) / α + τ) ∧
            (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
              10000000 * (((r : ℝ) + q) / α + τ) := by
  dsimp only
  let C := convexHull ℝ (range A)
  have hC := convex_convexHull ℝ (range A)
  let hb := positive_kernel_hull_properties A hA hApos
  let vhat := fittedValueSelection C hb.1 hb.2.1 hb.2.2
  have hAC : range A ⊆ C := subset_convexHull ℝ _
  have hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w) :=
    fun w _ ↦ fittedValueSelection_isMax C hb.1 hb.2.1 hb.2.2 w
  refine ⟨measurable_maximumExtremeSupport A hA hC hb.2.2 hAC vhat hvmax
    (canonicalFittedValue_continuousOn C hC hb.1 hb.2.1 hb.2.2), ?_⟩
  obtain ⟨G, hGmeas, hGprob, hG⟩ := effective_dimension_finite_support hq hη hscale
    hwidthScale C hC hb.1 hb.2.1 hb.2.2 (range A) (isCompact_range hA).isClosed
    hAC Subset.rfl V hrank hwidth
  refine ⟨G, hGmeas, hGprob, ?_⟩
  intro w hw
  obtain ⟨hcoord, hwpos, hs, hnonneg, hloss, hlog, hnear⟩ := hG w hw
  have heq := maximumExtremeSupport_eq_maximumIndependentSupport A hA hC hb.2.2
    hAC vhat hvmax w
  have hsfull : (maximumExtremeSupport A vhat w : ℝ) ≤ 10000000 * ((r : ℝ) + q) := by
    simpa only [heq] using hs
  refine ⟨hcoord, hwpos, hsfull,
    canonical_maximumExtremeSupport_attained A hA C hC hb.1 hb.2.1 hb.2.2 hAC
      Subset.rfl w hwpos, ?_, hnonneg, hloss, hlog, hnear⟩
  intro μ hext
  have hμ := full_extreme_optimizer_support_le_maximum A hA hC hb.2.2 hAC vhat hvmax
    w hwpos μ hext
  exact ⟨hμ.1, (Nat.cast_le.mpr hμ.2).trans hsfull⟩
