-- Prove2me | Definitions.Def_ReweightedNPMLE_GaussianSampling
-- name    : ReweightedNPMLE_GaussianSampling
-- status  : Definition
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:26:00.963822+00:00
-- url     : https://prove2.me/theorems/b17504a2-2d0a-5f0a-82f7-ee3457873af5
-- title:
--   Independent samples from a compact-location Gaussian mixture
-- statement:
--   For any \(K\subseteq\mathbb R^d\) and probability measure \(G_\star\) on \(K\), define
--   \[
--   f_{G_\star}(x)=\int_K(2\pi)^{-d/2}e^{-\|x-\theta\|^2/2}\,dG_\star(\theta),
--   \qquad P_{G_\star,n}=(f_{G_\star}\,dx)^{\otimes n}.
--   \]
--   Thus \(P_{G_\star,n}\) is the law of \(n\) independent observations with common mixture density \(f_{G_\star}\). The included identity equates this one-observation density law with the generative law obtained by adding independent standard Gaussian noise to a location drawn from \(G_\star\). The sample measure is a probability measure for every \(n\), including the empty sample. The construction itself does not require compactness of \(K\).
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianSampling.lean#L18-L37

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
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Gaussian sample laws and simultaneous genericity

The iid sample law has a density, is a probability law, and satisfies the
uniform paper-radius tail. The constants do not depend on the true compact
mixing law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace ReweightedNPMLE

noncomputable def compactGaussianSampleMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) : Measure (Fin n → Point d) :=
  Measure.pi (fun _ : Fin n ↦ volume.withDensity
    (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))

theorem compactGaussianMixtureLaw_eq_density {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) :
    gaussianLocationMixtureLaw (Gstar : Measure K) (fun a : K ↦ (a : Point d)) =
      volume.withDensity (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)) :=
  gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture _ _ measurable_subtype_coe

instance isProbabilityMeasure_compactGaussianSampleMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) :
    IsProbabilityMeasure (compactGaussianSampleMeasure Gstar n) := by
  letI : IsProbabilityMeasure (volume.withDensity
      (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y))) := by
    rw [← compactGaussianMixtureLaw_eq_density Gstar]
    exact gaussianLocationMixtureLaw_isProbability _ _ measurable_subtype_coe
  dsimp [compactGaussianSampleMeasure]
  infer_instance





end ReweightedNPMLE


