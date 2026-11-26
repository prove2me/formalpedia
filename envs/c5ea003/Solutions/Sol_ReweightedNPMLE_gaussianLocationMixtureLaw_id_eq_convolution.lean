-- Prove2me | solution 1 for ReweightedNPMLE.gaussianLocationMixtureLaw_id_eq_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:12:02.205809+00:00
-- url     : https://prove2.me/submissions/44274529-4406-46d8-9183-aa8dcac7607d

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Identifiability of Gaussian location mixtures

Convolution with a standard Gaussian is injective on probability measures:
its characteristic function is nowhere zero.  Combined with the generative-
law/density identity, this proves identifiability of the mixing law from the
mixture density.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The generative Gaussian-mixture law is convolution of the location law
with the standard Gaussian law. -/
theorem solution
    {d : ℕ} (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    gaussianLocationMixtureLaw μ id =
      (μ.prod (stdGaussian (Point d))).map (fun p ↦ p.1 + p.2) := by
  let γd : Measure (Fin d → ℝ) :=
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)
  rw [gaussianLocationMixtureLaw]
  change (μ.prod γd).map (fun q ↦ q.1 + WithLp.toLp 2 q.2) = _
  rw [show (μ.prod γd).map (fun q ↦ q.1 + WithLp.toLp 2 q.2) =
      ((μ.prod γd).map (Prod.map id (WithLp.toLp 2))).map
        (fun p ↦ p.1 + p.2) by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl]
  rw [← Measure.map_prod_map μ γd measurable_id (by fun_prop),
    Measure.map_id, ProbabilityTheory.map_pi_eq_stdGaussian]
