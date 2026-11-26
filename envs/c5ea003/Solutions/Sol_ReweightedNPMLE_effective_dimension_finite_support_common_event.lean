-- Prove2me | solution 1 for ReweightedNPMLE.effective_dimension_finite_support_common_event
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:14:33.840567+00:00
-- url     : https://prove2.me/submissions/d7269281-c9be-4a08-b125-c06364dd5110

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
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Real
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
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_canonical_maximumIndependentSupport_gamma_tail
import Theorems.Thm_ReweightedNPMLE_coordinateLog_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_exists_independentRepresentationEvent_of_mem_convexHull
import Theorems.Thm_ReweightedNPMLE_exists_local_positive_weight_lower_bound
import Theorems.Thm_ReweightedNPMLE_exists_uniform_positive_coordinate_bounds
import Theorems.Thm_ReweightedNPMLE_fittedValue_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_fitted_radial_localization
import Theorems.Thm_ReweightedNPMLE_gammaEffectiveEvent_failure_bound
import Theorems.Thm_ReweightedNPMLE_gammaEffectiveEvent_localization_bounds
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



theorem fittedLogDisplacement_eq {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (z₀ : Fin n → ℝ) {w : Fin n → ℝ} (hw : w ∈ positiveVectors n) :
    fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w =
      fittedLogSelection C hCcompact hCnonempty hCpos w - z₀ := by
  classical
  simp [fittedLogDisplacement, hw]





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

-- Inline helpers preserved from ReweightedNPMLE.GammaEffectiveEvent.
section
/-!
# Common Gamma concentration and localization event

The projected-energy and maximum-coordinate bounds hold jointly with
failure probability at most `2 exp(-q)`.  Explicit scale conditions imply
all radial localization hypotheses and the sharp `alpha E <= 2` width
cost bound.
-/

open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE







theorem isClosed_gammaEffectiveEvent {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℕ) (α q : ℝ) :
    IsClosed (gammaEffectiveEvent V r α q) := by
  have hc : IsClosed {w : Fin n → ℝ | ∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)} := by
    have heq : {w : Fin n → ℝ | ∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)} =
        ⋂ i : Fin n, {w : Fin n → ℝ | |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)} := by
      ext w
      simp
    rw [heq]
    exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const
  have hp : Continuous (fun w : Fin n → ℝ ↦ Real.sqrt α *
      ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖) := by fun_prop
  exact hc.inter (isClosed_le hp continuous_const)





end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.EffectiveSparsification.
section
/-!
# Effective-dimension sparsification on a common event

Gamma concentration instantiates radial localization and the determinant
support tail. All near-optimal fitted vectors obey the error bounds on the
same measurable event. The support statistic here is the maximum independent
finite representation; identification with full measure-fiber extreme points
is a separate theorem, not an assumption hidden in this result.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

theorem gammaEffectiveEvent_fitted_localization {n r : ℕ} [Nonempty (Fin n)]
    {α q η : ℝ} (hα : 0 < α) (hQ : 0 ≤ effectiveQ n q) (hN : 0 ≤ effectiveN r q)
    (hη : 0 ≤ η) (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (hαQ : 1024 * effectiveQ n q ≤ α)
    (hαN : 2359296 * effectiveN r q ≤ α) (hα₀ : 12288 ≤ α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hwidth : ∀ u ∈ relativeFittedSet C (fittedValueSelection C hCcompact hCnonempty hCpos 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η)
    {w : Fin n → ℝ} (hw : w ∈ gammaEffectiveEvent V r α q)
    (v : Fin n → ℝ) (hv : v ∈ C) (τ : ℝ) (hτ₀ : 0 ≤ τ) (hτ : τ < 1 / 3072)
    (hnear : weightedLogLikelihood w (fittedValueSelection C hCcompact hCnonempty hCpos w) - τ ≤
      weightedLogLikelihood w v) :
    let v₀ := fittedValueSelection C hCcompact hCnonempty hCpos 1
    (∀ i, |fittedLogRatio v₀ v i| ≤ 1 / 8) ∧
    0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
    α * (weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v) ≤
      592 * effectiveN r q + 26 + 13 * α * τ ∧
    α * (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
      1152 * effectiveN r q + 48 + 24 * α * τ ∧
    α * (∑ i, (w i - 1) * fittedLogRatio v₀ v i) ≤
      592 * effectiveN r q + 26 + 12 * α * τ := by
  let v₀ := fittedValueSelection C hCcompact hCnonempty hCpos 1
  have hb := gammaEffectiveEvent_localization_bounds hα hQ hN hη hwidthScale hαQ hαN hα₀ V hw
  have hv₀ := fittedValueSelection_isMax C hCcompact hCnonempty hCpos 1
  have hvw := fittedValueSelection_isMax C hCcompact hCnonempty hCpos w
  have hnear₀ : weightedLogLikelihood w v₀ - τ ≤ weightedLogLikelihood w v := by
    have hh := hvw.2 _ hv₀.1
    dsimp [v₀]
    linarith
  have hl := fitted_radial_localization hC hCpos v₀ hv₀ V η hη hwidth
    w v hv τ hτ₀ hb.1 hb.2.2.2.2.1 hb.2.2.2.2.2 (by norm_num at *; exact hτ) hnear₀
  refine ⟨hl.1, hl.2.1, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hl.2.2.1 hα.le
    nlinarith [hb.2.2.1, hb.2.2.2.1]
  · have hh := mul_le_mul_of_nonneg_left hl.2.2.2.1 hα.le
    nlinarith [hb.2.2.1, hb.2.2.2.1]
  · have hh := mul_le_mul_of_nonneg_left hl.2.2.2.2 hα.le
    nlinarith [hb.2.2.1, hb.2.2.2.1]











end ReweightedNPMLE
end

/-!
# Effective-dimension sparsification on a common event

Gamma concentration instantiates radial localization and the determinant
support tail. All near-optimal fitted vectors obey the error bounds on the
same measurable event. The support statistic here is the maximum independent
finite representation; identification with full measure-fiber extreme points
is a separate theorem, not an assumption hidden in this result.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution
    {n r : ℕ} [Nonempty (Fin n)] {α q η : ℝ}
    (hα : 0 < α) (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (hαQ : 1024 * effectiveQ n q ≤ α)
    (hαN : 2359296 * effectiveN r q ≤ α) (hα₀ : 12288 ≤ α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (hChull : C ⊆ convexHull ℝ D)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r)
    (hwidth : ∀ u ∈ relativeFittedSet C (fittedValueSelection C hCcompact hCnonempty hCpos 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
    let v₀ := vhat 1
    let k := maximumIndependentSupport D vhat
    ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
      ∀ w ∈ G, w ∈ gammaEffectiveEvent V r α q ∧ w ∈ positiveVectors n ∧ 0 < k w ∧
        Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ) < 1744 * effectiveN r q + 74 + q ∧
        ∀ (τ : ℝ), 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
          weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
          (∀ i, |fittedLogRatio v₀ v i| ≤ 1 / 8) ∧
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
          α * (weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v) ≤
            592 * effectiveN r q + 26 + 13 * α * τ ∧
          α * (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
            1152 * effectiveN r q + 48 + 24 * α * τ := by
  classical
  let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
  let v₀ := vhat 1
  let k := maximumIndependentSupport D vhat
  let E := gammaEffectiveEvent V r α q
  let H := 1744 * effectiveN r q + 74
  let z₀ := fittedLogSelection C hCcompact hCnonempty hCpos 1
  let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
  have hn1 : 1 ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n from Fin.pos_iff_nonempty.mpr inferInstance)
  have hQ : 0 ≤ effectiveQ n q := by
    have hh := Real.log_nonneg (show 1 ≤ 2 * (n : ℝ) by linarith)
    dsimp [effectiveQ]
    linarith
  have hN : 0 ≤ effectiveN r q := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    dsimp [effectiveN]
    positivity
  have hEmeas : MeasurableSet E := (isClosed_gammaEffectiveEvent V r α q).measurableSet
  have hEpos : E ⊆ positiveVectors n := fun w hw ↦
    (gammaEffectiveEvent_localization_bounds hα hQ hN hη hwidthScale hαQ hαN hα₀ V hw).2.1
  have hloc : ∀ w ∈ E,
      (∀ i, |fittedLogRatio v₀ (vhat w) i| ≤ 1 / 8) ∧
      α * (∑ i, (w i - 1) * fittedLogRatio v₀ (vhat w) i +
        ∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤ H := by
    intro w hw
    have hl := gammaEffectiveEvent_fitted_localization hα hQ hN hη hwidthScale
      hαQ hαN hα₀ C hC hCcompact hCnonempty hCpos V hwidth hw (vhat w)
      (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 0 (by norm_num)
      (by norm_num) (by simp [vhat])
    refine ⟨hl.1, ?_⟩
    dsimp [H]
    nlinarith [hl.2.2.2.1, hl.2.2.2.2]
  have htRatio : ∀ w ∈ E, t w = fittedLogRatio v₀ (vhat w) := by
    intro w hw
    rw [show t w = fittedLogSelection C hCcompact hCnonempty hCpos w - z₀ from
      fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ (hEpos hw)]
    rfl
  have ht : ∀ w ∈ E, ∀ i, |t w i| ≤ 1 / 8 := by
    intro w hw
    rw [htRatio w hw]
    exact (hloc w hw).1
  have hcost : ∀ w ∈ E,
      α * (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2) ≤ H := by
    intro w hw
    rw [htRatio w hw]
    exact (hloc w hw).2
  let B : Set (Fin n → ℝ) := {w | w ∈ E ∧ H + q ≤ Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ)}
  have hkmeas : Measurable k := measurable_maximumIndependentSupport D hDclosed vhat
    (canonicalFittedValue_continuousOn C hC hCcompact hCnonempty hCpos)
  have hcast : Measurable (fun w ↦ ((k w - 1 : ℕ) : ℝ)) :=
    (measurable_of_countable (fun j : ℕ ↦ (j : ℝ))).comp (hkmeas.sub_const 1)
  have hBmeas : MeasurableSet B := hEmeas.inter
    (measurableSet_le measurable_const (measurable_const.mul hcast))
  have hBprob : (gammaProductMeasure n α α).real B ≤ Real.exp (-q) :=
    canonical_maximumIndependentSupport_gamma_tail hα C hC hCcompact hCnonempty hCpos
      D hDclosed hD z₀ hEmeas hEpos ht H q hcost
  let G := E \ B
  refine ⟨G, hEmeas.diff hBmeas, ?_, ?_⟩
  · letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hα hα
    letI : IsProbabilityMeasure (gammaProductMeasure n α α) := by
      dsimp [gammaProductMeasure]
      infer_instance
    have hEprob := gammaEffectiveEvent_failure_bound hα hq
      (show 4 * effectiveQ n q ≤ α by linarith)
      (show 4 * effectiveN r q ≤ α by linarith) V hrank
    have hcover : Gᶜ ⊆ Eᶜ ∪ B := by
      intro w hw
      by_cases hwe : w ∈ E
      · right
        by_contra hwb
        exact hw ⟨hwe, hwb⟩
      · exact Or.inl hwe
    calc
      (gammaProductMeasure n α α).real Gᶜ ≤ (gammaProductMeasure n α α).real (Eᶜ ∪ B) :=
        measureReal_mono hcover
      _ ≤ (gammaProductMeasure n α α).real Eᶜ + (gammaProductMeasure n α α).real B :=
        measureReal_union_le _ _
      _ ≤ 3 * Real.exp (-q) := by linarith
  · intro w hw
    have hwpos := hEpos hw.1
    have hkpos := maximumIndependentSupport_pos_of_mem_convexHull C hC hCcompact
      hCnonempty hCpos D hD w hwpos
      (hChull (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1)
    have hsmall : Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ) < H + q :=
      lt_of_not_ge (fun hh ↦ hw.2 ⟨hw.1, hh⟩)
    refine ⟨hw.1, hwpos, hkpos, hsmall, ?_⟩
    intro τ hτ₀ hτ v hv hnear
    have hl := gammaEffectiveEvent_fitted_localization hα hQ hN hη hwidthScale
      hαQ hαN hα₀ C hC hCcompact hCnonempty hCpos V hwidth hw.1 v hv τ hτ₀ hτ hnear
    exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1⟩
