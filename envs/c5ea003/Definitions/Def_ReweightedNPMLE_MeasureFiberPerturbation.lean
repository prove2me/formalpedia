-- Prove2me | Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
-- name    : ReweightedNPMLE_MeasureFiberPerturbation
-- status  : Definition
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:24:30.236261+00:00
-- url     : https://prove2.me/theorems/d914a440-e2ff-53e8-a014-3ada3e2a81b7
-- title:
--   A probability measure obtained from a nonnegative real density
-- statement:
--   Let \(\mu\) be a probability measure and let \(f:\Theta\to\mathbb R\) be integrable, everywhere nonnegative, and normalized by \(\int f\,d\mu=1\). Define the probability measure \(\mu_f\) by
--   \[
--   d\mu_f=f\,d\mu,
--   \qquad
--   \mu_f(B)=\int_B f\,d\mu
--   \]
--   for measurable \(B\). The construction uses the nonnegative extended-real density associated with \(f\); the hypotheses ensure its total mass is one. It applies to arbitrary base probability laws, including laws with infinite support. In moment-preserving perturbations, densities of the form \(1\pm h\) generate two probability measures once their nonnegativity and normalization have been established.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/MeasureFiberPerturbation.lean#L18-L24

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
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
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
# Moment-preserving perturbations of probability measures

A bounded nonzero perturbation with zero mass and zero fitted moments gives
two genuine probability measures in the same full fiber whose average is
the original law. This applies to arbitrary, possibly infinite-support laws.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

noncomputable def probabilityMeasureWithRealDensity {Θ : Type*} [MeasurableSpace Θ]
    (μ : ProbabilityMeasure Θ) (f : Θ → ℝ) (hf : Integrable f (μ : Measure Θ))
    (hf₀ : ∀ x, 0 ≤ f x) (hfmean : ∫ x, f x ∂μ = 1) : ProbabilityMeasure Θ := by
  refine ⟨(μ : Measure Θ).withDensity (fun x ↦ ENNReal.ofReal (f x)), ⟨?_⟩⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf₀), hfmean]
  norm_num





end ReweightedNPMLE


