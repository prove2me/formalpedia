-- Prove2me | solution 1 for ReweightedNPMLE.pi_withDensity_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:03:03.422979+00:00
-- url     : https://prove2.me/submissions/3a866e6d-767a-4b8e-89ae-bf8eb3941abc

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_lintegral_fin_prod_eq_prod

/-!
# Scale invariance behind Gamma--Dirichlet independence

The normalized Gamma vector is unchanged by a common positive rescaling.
This file first proves the corresponding exact scaling laws for scalar and
finite-product Gamma measures.  These are the measure-theoretic core of the
remaining independence statement in Proposition 2.1.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- A finite product of absolutely continuous measures has density equal to
the product of the coordinate densities. -/
theorem solution {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ENNReal)
    (hf : ∀ i, Measurable (f i)) (hftop : ∀ i x, f i x ≠ ⊤) :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  letI (i : Fin n) : SigmaFinite ((μ i).withDensity (f i)) :=
    SigmaFinite.withDensity_of_ne_top' (hftop i)
  apply Measure.pi_eq
  intro s hs
  have hspi : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hspi]
  rw [← lintegral_indicator hspi]
  have hind : (Set.pi Set.univ s).indicator (fun x ↦ ∏ i, f i (x i)) =
      (fun x ↦ ∏ i, (s i).indicator (f i) (x i)) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · have hall : ∀ i, x i ∈ s i := by
        intro i
        exact (Set.mem_pi.mp hx) i (Set.mem_univ i)
      simp [hall]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        simpa only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] using hx
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact Set.indicator_of_notMem hi _
  rw [hind, lintegral_fin_prod_eq_prod _ (fun i ↦ (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
