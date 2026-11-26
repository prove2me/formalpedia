-- Prove2me | Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
-- name    : ReweightedNPMLE_ProbabilityFiberGeometry
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:24:05.826713+00:00
-- url     : https://prove2.me/theorems/a2c8c8ec-68f4-42d7-98b9-0d01c2d07dd2
-- title:
--   Extreme probability mixtures through continuous test functions
-- statement:
--   For a topological measurable space \(\Theta\), associate to each probability measure \(\mu\) its continuous-test-function evaluation vector
--   \[
--   I_\mu:C(\Theta,\mathbb R)\to\mathbb R,\qquad I_\mu(f)=\int f\,d\mu.
--   \]
--   The image of a mixture fiber is
--   \[
--   \mathcal I_A(v)=\{I_\mu:V_A(\mu)=v\}
--   \subseteq\mathbb R^{C(\Theta,\mathbb R)}.
--   \]
--   A probability mixture is defined to be extreme at fitted value \(v\) precisely when \(I_\mu\) is an extreme point of \(\mathcal I_A(v)\). On compact metric Borel parameter spaces, continuous test functions give a faithful affine representation of probability measures, so this expresses the usual absence of a nontrivial convex decomposition within the full probability fiber. The ambient function space carries its product vector-space structure.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ProbabilityFiberGeometry.lean#L20-L80

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

namespace ReweightedNPMLE

noncomputable def probabilityIntegralFunctional {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] (μ : ProbabilityMeasure Θ) : C(Θ, ℝ) → ℝ :=
  fun f ↦ ∫ θ, f θ ∂μ







def probabilityFiberImage {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) : Set (C(Θ, ℝ) → ℝ) :=
  probabilityIntegralFunctional '' probabilityMixtureFiber A v





def IsExtremeProbabilityMixture {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ) : Prop :=
  probabilityIntegralFunctional μ ∈ (probabilityFiberImage A v).extremePoints ℝ











end ReweightedNPMLE


