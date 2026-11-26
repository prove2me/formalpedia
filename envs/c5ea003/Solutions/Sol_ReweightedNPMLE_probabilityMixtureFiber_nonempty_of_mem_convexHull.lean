-- Prove2me | solution 1 for ReweightedNPMLE.probabilityMixtureFiber_nonempty_of_mem_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:13:56.373625+00:00
-- url     : https://prove2.me/submissions/5ddc6f7f-5972-49ec-93a7-751958ef63da

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
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureValue_finiteProbabilityMeasure

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
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (hv : v ∈ convexHull ℝ (range A)) : (probabilityMixtureFiber A v).Nonempty := by
  classical
  obtain ⟨ι, hι, p₀, B₀, hp₀, hpsum₀, hB₀, hvalue₀⟩ :=
    mem_convexHull_iff_exists_fintype.mp hv
  letI : Fintype ι := hι
  let m := Fintype.card ι
  let e : Fin m ≃ ι := (Fintype.equivFin ι).symm
  have hpre : ∀ j : Fin m, ∃ θ, A θ = B₀ (e j) := fun j ↦ hB₀ (e j)
  choose θ hθ using hpre
  let p : Fin m → ℝ := p₀ ∘ e
  have hp : p ∈ finiteSimplex m := ⟨fun j ↦ hp₀ (e j), (e.sum_comp p₀).trans hpsum₀⟩
  refine ⟨finiteProbabilityMeasure θ p hp, ?_⟩
  change probabilityMixtureValue A (finiteProbabilityMeasure θ p hp) = v
  rw [probabilityMixtureValue_finiteProbabilityMeasure A hA θ p hp]
  calc
    finiteMixtureValue (A ∘ θ) p = ∑ j : Fin m, p₀ (e j) • B₀ (e j) := by
      simp only [finiteMixtureValue, p, Function.comp_apply, hθ]
    _ = v := (e.sum_comp (fun j ↦ p₀ j • B₀ j)).trans hvalue₀
