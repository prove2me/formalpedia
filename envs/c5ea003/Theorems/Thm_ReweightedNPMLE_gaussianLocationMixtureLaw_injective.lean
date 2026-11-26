-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianLocationMixtureLaw_injective
-- name    : ReweightedNPMLE.gaussianLocationMixtureLaw_injective
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:47:10.369747+00:00
-- url     : https://prove2.me/theorems/4009362b-32c7-4c0e-9539-b6869cebc446
-- title:
--   Injectivity of Gaussian convolution on probability measures
-- statement:
--   Let $d\ge0$ be an integer and let $\mu,\nu$ be Borel probability measures on $\mathbb R^d$. Denote by $P_\mu$ and $P_\nu$ their Gaussian location-mixture laws with independent $N(0,I_d)$ noise. Then
--   $$
--   P_\mu=P_\nu\quad\Longrightarrow\quad\mu=\nu.
--   $$
--   No boundedness, compact-support, moment, or density assumption on the mixing measures is imposed.
--
--   Thus the observable Gaussian mixture distribution uniquely determines its mixing law. This is the identifiability input for recovering mixing-law convergence from density convergence.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianIdentifiability.lean#L49-L65

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

theorem ReweightedNPMLE.gaussianLocationMixtureLaw_injective
    {d : ℕ} (μ ν : Measure (Point d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : gaussianLocationMixtureLaw μ id =
      gaussianLocationMixtureLaw ν id) : μ = ν := by sorry
