-- Prove2me | Theorems.Thm_ReweightedNPMLE_mem_smallSupportProbabilityLaws_iff
-- name    : ReweightedNPMLE.mem_smallSupportProbabilityLaws_iff
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:48:19.396122+00:00
-- url     : https://prove2.me/theorems/5c20a0b1-e8ea-520c-9422-5d4a59de2df0
-- title:
--   Finite-atomic parameterization exactly characterizes small support
-- statement:
--   Let $\Theta$ be a compact metric space with its Borel structure, $m\ge0$, and $\mu\in\mathcal P(\Theta)$. Let $\mathcal A_m$ be the union, for $0\le k\le m$, of the images of the $k$-location simplex parameterizations $(\theta,p)\mapsto\sum_jp_j\delta_{\theta_j}$. Then $$\mu\in\mathcal A_m\quad\Longleftrightarrow\quad\operatorname{supp}\mu\text{ is finite and }|\operatorname{supp}\mu|\le m.$$ This connects a compact parameterized set of laws to the topological support property.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SmallSupportProbability.lean#L53-L75

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SmallSupportProbability
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Closed sets of probability laws with bounded finite support

The at-most-`m`-atom laws form a compact set in the weak topology. Finite
atomic laws are parameterized by compact atom lists and closed simplices,
including zero masses and coincident locations.
-/

open Set MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.mem_smallSupportProbabilityLaws_iff {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (m : ℕ) (μ : ProbabilityMeasure Θ) :
    μ ∈ smallSupportProbabilityLaws Θ m ↔
      (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ m := by sorry
