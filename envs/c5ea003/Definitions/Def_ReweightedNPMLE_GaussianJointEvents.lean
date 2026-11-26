-- Prove2me | Definitions.Def_ReweightedNPMLE_GaussianJointEvents
-- name    : ReweightedNPMLE_GaussianJointEvents
-- status  : Definition
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:25:39.23572+00:00
-- url     : https://prove2.me/theorems/cfbe4d0a-1f2f-5f91-a770-fa11b276d8d5
-- title:
--   Joint optimizer comparisons and structural failure events
-- statement:
--   For data \(x=(x_i)_{i=1}^n\), weights \(w\), and a location map \(\vartheta:\Theta\to\mathbb R^d\), write
--   \[
--   f_\mu(x)=\int_\Theta(2\pi)^{-d/2}e^{-\|x-\vartheta(a)\|^2/2}\,d\mu(a),
--   \quad \ell_w(\mu)=\sum_iw_i\log f_\mu(x_i).
--   \]
--   The optimizer set contains all probability laws maximizing \(\ell_w\). The comparison graph pairs a weighted optimizer \(\mu\) with an ordinary optimizer \(\nu\), using the same data. Define
--   \[
--   \Delta(\mu,\nu)=\ell_{\mathbf1}(\nu)-\ell_{\mathbf1}(\mu),\qquad
--   D(\mu,\nu)=\sum_i\log^2\!\frac{f_\mu(x_i)}{f_\nu(x_i)}.
--   \]
--   For real thresholds \(R,t,a\), the structural failure set is the union of five conditions: some weight is nonpositive or violates \(|w_i-1|\le a\); two weighted optimizer laws are distinct; some weighted optimizer lacks finite support of cardinality at most \(R\); some comparison pair has \(\Delta>t\); or some comparison pair has \(D>t\).
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianJointEvents.lean#L18-L169

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

namespace ReweightedNPMLE

abbrev GaussianDataWeight (d n : ℕ) := (Fin n → Point d) × (Fin n → ℝ)

noncomputable def gaussianProbabilityLogLikelihood {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (p : GaussianDataWeight d n × ProbabilityMeasure Θ) : ℝ :=
  weightedLogLikelihood p.1.2
    (probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2)

def gaussianProbabilityOptimizerSet {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (p : GaussianDataWeight d n) : Set (ProbabilityMeasure Θ) :=
  {μ | IsMaxOn univ (fun ν ↦ gaussianProbabilityLogLikelihood θ (p, ν)) μ}







def gaussianOptimizerComparisonGraph {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) :
    Set (GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) :=
  {p | p.2.1 ∈ gaussianProbabilityOptimizerSet θ p.1 ∧
    p.2.2 ∈ gaussianProbabilityOptimizerSet θ (p.1.1, 1)}



noncomputable def gaussianOrdinaryLikelihoodGap {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) : ℝ :=
  gaussianProbabilityLogLikelihood θ ((p.1.1, 1), p.2.2) -
    gaussianProbabilityLogLikelihood θ ((p.1.1, 1), p.2.1)





noncomputable def gaussianSquaredLogRatioGap {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) : ℝ :=
  ∑ i, (Real.log
    (probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.1 i /
     probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.2 i)) ^ 2





noncomputable def gaussianStructuralFailure {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (R t a : ℝ) : Set (GaussianDataWeight d n) :=
  {p | ¬((∀ i, |p.2 i - 1| ≤ a) ∧ p.2 ∈ positiveVectors n)} ∪
  {p | ∃ μ ν : ProbabilityMeasure Θ, μ ∈ gaussianProbabilityOptimizerSet θ p ∧
    ν ∈ gaussianProbabilityOptimizerSet θ p ∧ μ ≠ ν} ∪
  {p | ∃ μ : ProbabilityMeasure Θ, μ ∈ gaussianProbabilityOptimizerSet θ p ∧
    ¬((μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R)} ∪
  {p | ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
    (p, μ) ∈ gaussianOptimizerComparisonGraph θ ∧ t < gaussianOrdinaryLikelihoodGap θ (p, μ)} ∪
  {p | ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
    (p, μ) ∈ gaussianOptimizerComparisonGraph θ ∧ t < gaussianSquaredLogRatioGap θ (p, μ)}





end ReweightedNPMLE


