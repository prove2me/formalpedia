-- Prove2me | solution 1 for ReweightedNPMLE.canonical_maximumIndependentSupport_gamma_moment
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:07:54.294433+00:00
-- url     : https://prove2.me/submissions/c2922358-2840-4763-b79e-3f21bd5a5069

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
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_canonicalFittedLog_ae_differentiableAt
import Theorems.Thm_ReweightedNPMLE_canonical_maximumIndependentSupport_jacobian_determinant_lower
import Theorems.Thm_ReweightedNPMLE_coordinateLog_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_exists_local_positive_weight_lower_bound
import Theorems.Thm_ReweightedNPMLE_exists_uniform_positive_coordinate_bounds
import Theorems.Thm_ReweightedNPMLE_fittedLog_monotone
import Theorems.Thm_ReweightedNPMLE_fittedValue_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_gamma_determinant_moment_of_monotone_ae_deriv
import Theorems.Thm_ReweightedNPMLE_measurable_maximumIndependentSupport
import Theorems.Thm_ReweightedNPMLE_multiplicativeChangeDeriv_toMatrix

-- Inline helpers preserved from ReweightedNPMLE.ChangeOfVariables.
section
/-!
# Injective change of variables for determinant moments

This file packages the precise area-formula step used by the paper's
determinant-moment argument.  If an injective differentiable map sends a
localized event into a probability density, its density-weighted Jacobian
has integral at most one.  A pointwise Jacobian/density comparison then
transfers that bound to the desired random variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ReweightedNPMLE

















/-- The basis-free determinant of a continuous linear endomorphism agrees
with the determinant of its standard-basis matrix. -/
theorem continuousLinearMap_det_eq_toMatrix'
    {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    L.det = (LinearMap.toMatrix' L.toLinearMap).det := by
  rw [ContinuousLinearMap.det, LinearMap.det_toMatrix']



















end ReweightedNPMLE
end

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







theorem isOpen_positiveVectors (n : ℕ) : IsOpen (positiveVectors n) := by
  have heq : positiveVectors n = ⋂ i : Fin n, {w : Fin n → ℝ | 0 < w i} := by
    ext w
    simp [positiveVectors]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)



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

theorem measurable_fittedLogDisplacement
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (z₀ : Fin n → ℝ) :
    Measurable (fittedLogDisplacement C hCcompact hCnonempty hCpos z₀) := by
  classical
  exact ((canonicalFittedLog_continuousOn C hC hCcompact hCnonempty hCpos).sub
    continuous_const.continuousOn).measurable_piecewise
      continuous_const.continuousOn (isOpen_positiveVectors n).measurableSet

theorem fittedLogDisplacement_hasFDerivAt
    {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (z₀ : Fin n → ℝ) {w : Fin n → ℝ} (hw : w ∈ positiveVectors n)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fittedLogSelection C hCcompact hCnonempty hCpos) J w) :
    HasFDerivAt (fittedLogDisplacement C hCcompact hCnonempty hCpos z₀) J w := by
  apply (hz.sub_const z₀).congr_of_eventuallyEq
  filter_upwards [(isOpen_positiveVectors n).mem_nhds hw] with q hq
  exact fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ hq

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

/-!
# Canonical fitted-value determinant moment

The Gamma determinant moment is proved for a compact positive convex fitted
set and any measurable cardinality function realized by full-support extreme
finite representations.  The representing atoms and coefficients may vary
with the weights, and need not be measurable choices.  All analytic and
change-of-variables hypotheses follow from canonical fitted-value regularity
and support sensitivity.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The determinant moment for the maximum independent support statistic.
Neither a measurable support statistic nor a selected extreme representation
is supplied as an assumption; both its measurability and its Jacobian gain
come from the representation geometry. -/
theorem solution
    {n : ℕ} [Nonempty (Fin n)] {α : ℝ} (hα : 0 < α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (z₀ : Fin n → ℝ)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) (hspos : s ⊆ positiveVectors n)
    (ht : ∀ w ∈ s, ∀ i,
      |fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i| ≤ 1 / 8) :
    let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
    let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
    ∫⁻ w in s, ENNReal.ofReal
        ((17 / 9 : ℝ) ^ (k w - 1) * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  let z := fittedLogSelection C hCcompact hCnonempty hCpos
  let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
  let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
  let J := fderiv ℝ z
  have hdiff := canonicalFittedLog_ae_differentiableAt C hC hCcompact hCnonempty hCpos
  apply gamma_determinant_moment_of_monotone_ae_deriv hα hs t
    (fun w ↦ (17 / 9 : ℝ) ^ (k w - 1)) J
  · filter_upwards [hdiff] with w hw hws
    exact fittedLogDisplacement_hasFDerivAt C hCcompact hCnonempty hCpos z₀
      (hspos hws) (hw (hspos hws)).hasFDerivAt
  · exact measurable_fittedLogDisplacement C hC hCcompact hCnonempty hCpos z₀
  · exact ((measurable_maximumIndependentSupport D hDclosed
      (fittedValueSelection C hCcompact hCnonempty hCpos)
      (canonicalFittedValue_continuousOn C hC hCcompact hCnonempty hCpos)).sub_const 1).const_pow _
  · exact fun w hws ↦ hspos hws
  · exact ht
  · intro w hws v hvs
    have hmon := fittedLog_monotone
      (fittedValueSelection C hCcompact hCnonempty hCpos)
      (s := s) (fun q _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos q)
      w hws v hvs
    dsimp only [t]
    rw [fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ (hspos hws),
      fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ (hspos hvs)]
    simpa only [fittedLogSelection, Pi.sub_apply, sub_sub_sub_cancel_right] using hmon
  · intro w hws
    positivity
  · filter_upwards [hdiff] with w hw hws
    have ha0 : ∀ i, 0 < 1 + t w i := by
      intro i
      have hi := neg_le_of_abs_le (ht w hws i)
      norm_num at hi ⊢
      linarith
    have haUpper : ∀ i, 1 + t w i ≤ 9 / 8 := by
      intro i
      have hi := le_of_abs_le (ht w hws i)
      norm_num at hi ⊢
      linarith
    have hd := canonical_maximumIndependentSupport_jacobian_determinant_lower
      C hC hCcompact hCnonempty hCpos D hD w (hspos hws)
      (hw (hspos hws)).hasFDerivAt (fun i ↦ 1 + t w i) ha0 haUpper
    rw [continuousLinearMap_det_eq_toMatrix', multiplicativeChangeDeriv_toMatrix]
    exact hd.trans (le_abs_self _)
