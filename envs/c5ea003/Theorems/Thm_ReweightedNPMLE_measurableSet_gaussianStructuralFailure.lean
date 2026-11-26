-- Prove2me | Theorems.Thm_ReweightedNPMLE_measurableSet_gaussianStructuralFailure
-- name    : ReweightedNPMLE.measurableSet_gaussianStructuralFailure
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:49:33.101415+00:00
-- url     : https://prove2.me/theorems/54287cef-452a-5ea7-bbde-06ac087e93f1
-- title:
--   Borel measurability of the joint structural failure event
-- statement:
--   Let $\Theta$ be a nonempty compact metric space with its Borel measurable structure and let $\theta:\Theta\to\mathbb R^d$ be continuous. Write $f_\mu(x)=\int\varphi_d(x-\theta(a))\,d\mu(a)$ and $L_w(\mu)=\sum_iw_i\log f_\mu(x_i)$ for probability laws $\mu$ on $\Theta$. Write $\Delta(\mu,\mu_0)=L_1(\mu_0)-L_1(\mu)$ and $J(\mu,\mu_0)=\sum_i[\log(f_\mu(x_i)/f_{\mu_0}(x_i))]^2$. The structural failure set $F(R,t,a)$ consists of data–weight pairs for which some coordinate satisfies $w_i\le0$ or $|w_i-1|>a$, the weighted optimizer is nonunique, some optimizer lacks finite support of cardinality at most $R$, or some weighted/ordinary optimizer pair has $\Delta>t$ or $J>t$. For every $R\ge0$ and real $t,a$, $$F(R,t,a)\text{ is Borel measurable}.$$ This combines full-law optimizer geometry and comparison inequalities into one joint event suitable for integration over data and weights.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianJointEvents.lean#L171-L195

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

theorem ReweightedNPMLE.measurableSet_gaussianStructuralFailure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) {R : ℝ} (hR : 0 ≤ R) (t a : ℝ) :
    MeasurableSet (gaussianStructuralFailure (n := n) θ R t a) := by sorry
