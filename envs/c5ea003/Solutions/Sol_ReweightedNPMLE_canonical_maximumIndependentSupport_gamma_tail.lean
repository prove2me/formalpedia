-- Prove2me | solution 1 for ReweightedNPMLE.canonical_maximumIndependentSupport_gamma_tail
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:08:44.220684+00:00
-- url     : https://prove2.me/submissions/7ee44148-87f8-4d8b-9866-89da57804877

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
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
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
import Theorems.Thm_ReweightedNPMLE_canonical_maximumIndependentSupport_gamma_moment
import Theorems.Thm_ReweightedNPMLE_coordinateLog_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_exists_local_positive_weight_lower_bound
import Theorems.Thm_ReweightedNPMLE_exists_uniform_positive_coordinate_bounds
import Theorems.Thm_ReweightedNPMLE_fittedValue_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_measurable_maximumIndependentSupport

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





















/-- Measurability of the Gamma determinant-moment integrand follows from
measurability of the displacement and determinant factor. -/
theorem measurable_gammaDeterminantIntegrand
    {n : ℕ} {α : ℝ}
    {t : (Fin n → ℝ) → (Fin n → ℝ)} {c : (Fin n → ℝ) → ℝ}
    (ht : Measurable t) (hc : Measurable c) :
    Measurable (fun w ↦ ENNReal.ofReal
      (c w * Real.exp (-α *
        (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))) := by
  fun_prop















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

-- Inline helpers preserved from ReweightedNPMLE.EffectiveDimension.
section
/-!
# Probability assembly for effective-dimension sparsification

This file formalizes the Markov and event-union steps used after the radial
localization and determinant-moment estimates in Theorem 3.1.
-/

open MeasureTheory Set

namespace ReweightedNPMLE









theorem markov_event_bound_exp_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ENNReal) (E : Set Ω) (q : ℝ)
    (hYmeas : Measurable Y) (hmean : ∫⁻ ω, Y ω ∂μ ≤ 1)
    (hlarge : E ⊆ {ω | ENNReal.ofReal (Real.exp q) ≤ Y ω}) :
    μ.real E ≤ Real.exp (-q) := by
  have hε : ENNReal.ofReal (Real.exp q) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos q)
  have hbound : μ E ≤ 1 / ENNReal.ofReal (Real.exp q) := by
    calc
      μ E ≤ μ {ω | ENNReal.ofReal (Real.exp q) ≤ Y ω} := measure_mono hlarge
      _ ≤ (∫⁻ ω, Y ω ∂μ) / ENNReal.ofReal (Real.exp q) :=
        meas_ge_le_lintegral_div hYmeas.aemeasurable hε ENNReal.ofReal_ne_top
      _ ≤ 1 / ENNReal.ofReal (Real.exp q) := by gcongr
  rw [one_div, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos q), ← Real.exp_neg] at hbound
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa [measureReal_def, (Real.exp_pos (-q)).le] using hh



end ReweightedNPMLE
end

/-!
# Probability assembly for effective-dimension sparsification

This file formalizes the Markov and event-union steps used after the radial
localization and determinant-moment estimates in Theorem 3.1.
-/

open MeasureTheory Set

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution
    {n : ℕ} [Nonempty (Fin n)] {α : ℝ} (hα : 0 < α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (z₀ : Fin n → ℝ)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) (hspos : s ⊆ positiveVectors n)
    (ht : ∀ w ∈ s, ∀ i,
      |fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i| ≤ 1 / 8)
    (H q : ℝ)
    (hcost : ∀ w ∈ s,
      α * (∑ i, (w i - 1) * fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i +
        ∑ i, (fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i) ^ 2) ≤ H) :
    let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
    (gammaProductMeasure n α α).real {w | w ∈ s ∧
      H + q ≤ Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ)} ≤ Real.exp (-q) := by
  classical
  let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
  let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
  let Y₀ : (Fin n → ℝ) → ENNReal := fun w ↦ ENNReal.ofReal
    ((17 / 9 : ℝ) ^ (k w - 1) * Real.exp (-α *
      (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
  let Y := s.indicator Y₀
  have htmeas := measurable_fittedLogDisplacement C hC hCcompact hCnonempty hCpos z₀
  have hkmeas := measurable_maximumIndependentSupport D hDclosed
    (fittedValueSelection C hCcompact hCnonempty hCpos)
    (canonicalFittedValue_continuousOn C hC hCcompact hCnonempty hCpos)
  have hY₀meas : Measurable Y₀ := measurable_gammaDeterminantIntegrand
    htmeas ((hkmeas.sub_const 1).const_pow _)
  apply markov_event_bound_exp_lintegral (gammaProductMeasure n α α) Y _ q (hY₀meas.indicator hs)
  · rw [lintegral_indicator hs]
    exact canonical_maximumIndependentSupport_gamma_moment
      hα C hC hCcompact hCnonempty hCpos D hDclosed hD z₀ hs hspos ht
  · intro w hw
    rcases hw with ⟨hws, hlarge⟩
    change ENNReal.ofReal (Real.exp q) ≤ Y w
    rw [show Y w = Y₀ w from indicator_of_mem hws Y₀]
    apply ENNReal.ofReal_le_ofReal
    change Real.exp q ≤ (17 / 9 : ℝ) ^ (k w - 1) * Real.exp (-α *
      (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2))
    have hpow : (17 / 9 : ℝ) ^ (k w - 1) =
        Real.exp (Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ)) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 17 / 9)]
    rw [hpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc := hcost w hws
    change α * (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2) ≤ H at hc
    linarith
