-- Prove2me | Theorems.Thm_ReweightedNPMLE_notMem_gaussianStructuralFailure_of_unique_optimizer
-- name    : ReweightedNPMLE.notMem_gaussianStructuralFailure_of_unique_optimizer
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:48:29.905606+00:00
-- url     : https://prove2.me/theorems/926ebcda-d987-5cc6-a1c5-b794098b5447
-- title:
--   Structural success from a unique optimizer and comparison bounds
-- statement:
--   Let $\Theta$ carry a topology and measurable structure, let $\theta:\Theta\to\mathbb R^d$, and define $L_w$, $\Delta=L_1(\mu_0)-L_1(\mu)$, and $J=\sum_i[\log(f_\mu(x_i)/f_{\mu_0}(x_i))]^2$ from the Gaussian mixture densities. Suppose $w_i>0$, $|w_i-1|\le a$, and the full weighted optimizer set is $\{\mu\}$. If $\operatorname{supp}\mu$ is finite with cardinality at most $R$, and every ordinary optimizer $\mu_0$ satisfies $\Delta,J\le t$, then $$(x,w)\notin F(R,t,a).$$ No compactness, continuity, or injectivity assumption is required for this logical implication.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianJointEvents.lean#L197-L229

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianJointEvents
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SmallSupportProbability
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Joint Borel events for Gaussian optimizer laws

All events concern the full probability-law optimizer space. Compact law
projection proves measurability of nonuniqueness, support failure, and
ordinary likelihood and fitted-log failures jointly in data and weights.
-/

open Set MeasureTheory
open scoped Topology BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.notMem_gaussianStructuralFailure_of_unique_optimizer {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {d n : ℕ}
    (θ : Θ → Point d) (x : Fin n → Point d) (w : Fin n → ℝ) (R t a : ℝ)
    (hcoord : ∀ i, |w i - 1| ≤ a) (hw : w ∈ positiveVectors n)
    (μ : ProbabilityMeasure Θ) (hunique : gaussianProbabilityOptimizerSet θ (x, w) = {μ})
    (hfinite : (μ : Measure Θ).support.Finite) (hcard : ((μ : Measure Θ).support.ncard : ℝ) ≤ R)
    (hcompare : ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1),
      gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, μ₀)) ≤ t ∧
      gaussianSquaredLogRatioGap θ ((x, w), (μ, μ₀)) ≤ t) :
    (x, w) ∉ gaussianStructuralFailure θ R t a := by sorry
