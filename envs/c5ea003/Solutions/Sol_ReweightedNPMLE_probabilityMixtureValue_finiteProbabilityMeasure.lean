-- Prove2me | solution 1 for ReweightedNPMLE.probabilityMixtureValue_finiteProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:53:54.911771+00:00
-- url     : https://prove2.me/submissions/73eecd6c-4107-488d-b3e2-f2fe9b5ac45f

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
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {m n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) :
    probabilityMixtureValue A (finiteProbabilityMeasure θ p hp) =
      finiteMixtureValue (A ∘ θ) p := by
  funext i
  change (∫ a, A a i ∂(∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j))) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,
      ENNReal.toReal_ofReal (hp.1 _), finiteMixtureValue, Function.comp_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_dirac' (fun a ↦ A a i) (θ j) ((continuous_apply i).comp hA).stronglyMeasurable]
  · intro j _
    letI := IsFiniteMeasureOnCompacts.smul (Measure.dirac (θ j))
      (c := ENNReal.ofReal (p j)) ENNReal.ofReal_ne_top
    exact ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := ENNReal.ofReal (p j) • Measure.dirac (θ j))
