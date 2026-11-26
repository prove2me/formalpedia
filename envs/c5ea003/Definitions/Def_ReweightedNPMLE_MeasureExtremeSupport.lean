-- Prove2me | Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
-- name    : ReweightedNPMLE_MeasureExtremeSupport
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:25:18.86806+00:00
-- url     : https://prove2.me/theorems/4c54c7c9-110f-5e08-9baa-85359ef8300f
-- title:
--   Full-fiber extreme support events and their supremum
-- statement:
--   For a dictionary \(A:\Theta\to\mathbb R^n\) and fitted-value map \(\widehat v\), define
--   \[
--   E_k^{\mathrm{ext}}
--   =\{w\in\mathbb R_{++}^n:\exists\mu,\
--   \mu\text{ is extreme in the full fiber at }\widehat v(w),\
--   \operatorname{ncard}(\operatorname{supp}\mu)=k\}.
--   \]
--   Define \(S_*(w)=\sup_{\mathbb N}\{k:w\in E_k^{\mathrm{ext}}\}\). The support is the topological support of the probability measure. The formal finite-cardinality operation assigns zero to an infinite set; the natural-number supremum likewise returns zero for an empty or unbounded set. Under the geometric hypotheses used in the support theorems, extreme supports are finite and this supremum is an attained maximum bounded by \(n\). The statistic is zero outside the positive weight orthant.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/MeasureExtremeSupport.lean#L19-L32

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Maximum support of full probability-measure extreme optimizers

The statistic is defined directly from arbitrary probability measures, not
from finite representations. The full extreme-optimizer characterization
identifies each cardinality event with the independent representation event.
Consequently its supremum is a measurable, attained maximum bounded by `n`.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

/-- Positive weights admitting a full-fiber extreme law of support size `k`. -/
def fullExtremeSupportEvent {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (k : ℕ) : Set (Fin n → ℝ) :=
  {w | w ∈ positiveVectors n ∧ ∃ μ : ProbabilityMeasure Θ,
    IsExtremeProbabilityMixture A (vhat w) μ ∧ (μ : Measure Θ).support.ncard = k}

/-- The paper's maximum extreme-optimizer support statistic, extended by zero
outside positive weights. Finiteness and attainment are proved below. -/
noncomputable def maximumExtremeSupport {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w : Fin n → ℝ) : ℕ :=
  sSup {k | w ∈ fullExtremeSupportEvent A vhat k}













end ReweightedNPMLE


