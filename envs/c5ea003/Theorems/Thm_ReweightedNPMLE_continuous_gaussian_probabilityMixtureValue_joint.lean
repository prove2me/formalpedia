-- Prove2me | Theorems.Thm_ReweightedNPMLE_continuous_gaussian_probabilityMixtureValue_joint
-- name    : ReweightedNPMLE.continuous_gaussian_probabilityMixtureValue_joint
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:44:33.952841+00:00
-- url     : https://prove2.me/theorems/28bd7c94-c389-420f-b1f3-cc41e714afe4
-- title:
--   Joint continuity of fitted Gaussian mixtures in data and mixing law
-- statement:
--   Let $d,n\ge0$ be integers, let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $\theta:\Theta\to\mathbb R^d$ be continuous. With $\varphi_d$ denoting the standard Gaussian density, define
--   $$
--   f_\mu(x)=\int_\Theta\varphi_d(x-\theta(a))\,d\mu(a)
--   \qquad(\mu\in\mathcal P(\Theta)).
--   $$
--
--   The fitted-value map
--   $$
--   ((x_1,\ldots,x_n),\mu)\longmapsto
--   \bigl(f_\mu(x_1),\ldots,f_\mu(x_n)\bigr)
--   $$
--   is continuous when data vectors have their Euclidean topology and mixing laws have the weak topology.
--
--   This joint continuity supports closed optimizer graphs and measurable simultaneous statistical events involving both the data and the full mixing law.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ParameterizedProbabilityIntegral.lean#L58-L85

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
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Joint continuity of compact-parameter probability integrals

Weak convergence of the law and uniform convergence of the integrand can
vary simultaneously. The probability normalization bounds the integral of
the varying integrand difference by its supremum norm.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.continuous_gaussian_probabilityMixtureValue_joint {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (fun p : (Fin n → Point d) × ProbabilityMeasure Θ ↦
      probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1 i) (θ a)) p.2) := by sorry
