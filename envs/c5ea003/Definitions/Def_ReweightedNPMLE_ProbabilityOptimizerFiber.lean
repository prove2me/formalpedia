-- Prove2me | Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
-- name    : ReweightedNPMLE_ProbabilityOptimizerFiber
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:18:52.064571+00:00
-- url     : https://prove2.me/theorems/a5f976b1-fdd1-595f-b1fb-e4cb3c30cd7f
-- title:
--   Probability-measure mixture fibers and convex combinations
-- statement:
--   For a measurable parameter space \(\Theta\), a dictionary \(A:\Theta\to\mathbb R^n\), and a probability measure \(\mu\), define the fitted vector coordinatewise by
--   \[
--   V_A(\mu)_i=\int_\Theta A_i(\theta)\,d\mu(\theta).
--   \]
--   The full probability fiber at \(v\) is \(\mathcal P_A(v)=\{\mu:V_A(\mu)=v\}\). For nonnegative \(a,b\) with \(a+b=1\), the probability convex combination is the measure \(a\mu+b\nu\). Given a finite probability vector \(p\) and locations \(\theta_j\), the associated finite probability measure is \(\sum_jp_j\delta_{\theta_j}\). These definitions allow finite atomic laws and arbitrary probability laws to be treated in the same fiber. Integrability and continuity assumptions on the dictionary are supplied when deriving affine or topological properties.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ProbabilityOptimizerFiber.lean#L24-L79

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
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

noncomputable def probabilityMixtureValue {Θ : Type*} [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (μ : ProbabilityMeasure Θ) : Fin n → ℝ :=
  fun i ↦ ∫ θ, A θ i ∂μ

def probabilityMixtureFiber {Θ : Type*} [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) : Set (ProbabilityMeasure Θ) :=
  {μ | probabilityMixtureValue A μ = v}

noncomputable def probabilityConvexCombination {Θ : Type*} [MeasurableSpace Θ]
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ) : ProbabilityMeasure Θ := by
  refine ⟨a • (μ : Measure Θ) + b • (ν : Measure Θ), ⟨?_⟩⟩
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ]
  change (a : ℝ≥0∞) * 1 + (b : ℝ≥0∞) * 1 = 1
  rw [mul_one, mul_one]
  rw [← ENNReal.coe_add, hab]
  rfl





noncomputable def finiteProbabilityMeasure {Θ : Type*} [MeasurableSpace Θ] {m : ℕ}
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) : ProbabilityMeasure Θ := by
  refine ⟨∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j), ⟨?_⟩⟩
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hp.1 j), hp.2]
  simp

























end ReweightedNPMLE


