-- Prove2me | solution 1 for ReweightedNPMLE.compactGaussianSampleMeasure_paper_radius_tail
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:11:11.006067+00:00
-- url     : https://prove2.me/submissions/b39f17df-f69f-46e4-a99a-1a55ed7e5de2

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_GaussianSampling
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_gaussianLocationMixtureSample_max_radius_tail
import Theorems.Thm_ReweightedNPMLE_gaussianPaper_failure_bound

/-!
# Gaussian sample laws and simultaneous genericity

The iid sample law has a density, is a probability law, and satisfies the
uniform paper-radius tail. The constants do not depend on the true compact
mixing law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {d n : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (hKbound : ∀ a ∈ K, ‖a‖ ≤ S) (hlog : 0 < Real.log (n : ℝ)) (hn : 1 ≤ n) :
    (compactGaussianSampleMeasure Gstar n).real
      {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} ≤
        (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
  let R := gaussianPaperRadiusExponent b n
  have hR : 0 < R := by dsimp [R, gaussianPaperRadiusExponent]; positivity
  have ht : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by positivity)
  have htail := gaussianLocationMixtureSample_max_radius_tail (n := n) (Gstar : Measure K)
    (fun a : K ↦ (a : Point d)) measurable_subtype_coe
    (fun a ↦ hKbound a.val a.property) ht
  rw [compactGaussianMixtureLaw_eq_density Gstar] at htail
  have htail' : (compactGaussianSampleMeasure Gstar n).real
      {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} ≤
        2 * (n : ℝ) * d * Real.exp (-R) := by
    have hsqrt : (Real.sqrt (2 * R)) ^ 2 = 2 * R := Real.sq_sqrt (by positivity)
    change (compactGaussianSampleMeasure Gstar n).real
      {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} ≤
        2 * (n : ℝ) * d * Real.exp (-(Real.sqrt (2 * R)) ^ 2 / 2) at htail
    rwa [hsqrt, show -(2 * R) / 2 = -R by ring] at htail
  have hfail := gaussianPaper_failure_bound d n hb hn
  have hterm : 0 ≤ Real.exp (-(b + 2) * Real.log (n : ℝ) - 1) := (Real.exp_pos _).le
  exact htail'.trans (by linarith)
