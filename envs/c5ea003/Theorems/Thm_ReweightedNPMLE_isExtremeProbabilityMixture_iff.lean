-- Prove2me | Theorems.Thm_ReweightedNPMLE_isExtremeProbabilityMixture_iff
-- name    : ReweightedNPMLE.isExtremeProbabilityMixture_iff
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:37:19.940938+00:00
-- url     : https://prove2.me/theorems/92c7f14b-1125-487c-8c2e-0c26a9070506
-- title:
--   Convex-combination characterization of extreme probability-mixture laws
-- statement:
--   Let $\Theta$ be a compact topological space with its Borel $\sigma$-algebra. Assume every closed-set indicator is the pointwise limit of a sequence of continuous $[0,1]$-valued functions that equal one on that closed set; in particular, compact metric spaces satisfy this condition. Let $n\ge0$, let $A:\Theta\to\mathbb R^n$ be any feature map, and let $v\in\mathbb R^n$ and $\mu\in\mathcal P(\Theta)$.
--
--   Write $\mathcal F_A(v)=\{\nu:\int A\,d\nu=v\}$. Define extremality using the injective integration-functional representation $I_\nu(f)=\int f\,d\nu$, $f\in C(\Theta,\mathbb R)$. Then $\mu$ is extreme in that represented fiber if and only if $\mu\in\mathcal F_A(v)$ and
--   $$
--   \left.
--   \begin{gathered}
--   a,b>0,\quad a+b=1,\quad \nu,\rho\in\mathcal F_A(v),\\
--   a\nu+b\rho=\mu
--   \end{gathered}
--   \right\}
--   \quad\Longrightarrow\quad\nu=\mu.
--   $$
--
--   This identifies the functional-space definition of extremality with the usual probability-measure decomposition test.
--
--   **Formalization Note** Continuity or integrability of $A$ is not an assumption of this equivalence. Its fiber uses the formalization's total coordinatewise Bochner integral, which is set to zero for a nonintegrable coordinate. In applications here, $A$ is continuous on a compact space and the integrals are ordinary finite integrals.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ProbabilityFiberGeometry.lean#L89-L118

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
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Real-vector-space geometry of full probability fibers

Integration against continuous test functions embeds probability measures
injectively into a locally convex real vector space with its product topology.
The weakly compact mixture fiber has a compact convex image. Extreme points
are thus mathlib extreme points of a faithful representation of the full
probability-measure fiber, rather than of a finite coefficient simplex.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.isExtremeProbabilityMixture_iff {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [HasOuterApproxClosed Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ) :
    IsExtremeProbabilityMixture A v μ ↔ μ ∈ probabilityMixtureFiber A v ∧
      ∀ (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
        (ν ρ : ProbabilityMeasure Θ), ν ∈ probabilityMixtureFiber A v →
        ρ ∈ probabilityMixtureFiber A v →
        probabilityConvexCombination a b hab ν ρ = μ → ν = μ := by sorry
