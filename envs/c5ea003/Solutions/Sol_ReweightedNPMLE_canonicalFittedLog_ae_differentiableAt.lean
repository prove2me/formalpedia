-- Prove2me | solution 1 for ReweightedNPMLE.canonicalFittedLog_ae_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:01:18.481456+00:00
-- url     : https://prove2.me/submissions/1df3498f-9939-41ad-9011-4d39b72c904f

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_coordinateLog_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_exists_uniform_positive_coordinate_bounds
import Theorems.Thm_ReweightedNPMLE_fittedValue_lipschitzOn

-- Inline helpers preserved from ReweightedNPMLE.FittedRegularity.
section
/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

namespace ReweightedNPMLE



theorem fittedValueSelection_isMax {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) :
    IsMaxOn C (weightedLogLikelihood w)
      (fittedValueSelection C hCcompact hCnonempty hCpos w) :=
  Classical.choose_spec (exists_fittedValue_maximizer hCcompact hCnonempty hCpos w)













/-- Quantitative local Lipschitz bound for the fitted log-vector. -/
theorem fittedLog_lipschitzOn {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {a c B : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ w ∈ s, ∀ i, a ≤ w i)
    (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hvB : ∀ w ∈ s, ∀ i, vhat w i ≤ B)
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    LipschitzOnWith
      ⟨((n : ℝ) * B ^ 2 / (a * c)) / c, by positivity⟩
      (fun w i ↦ Real.log (vhat w i)) s := by
  exact coordinateLog_lipschitzOn vhat hc hvc
    (fittedValue_lipschitzOn hC hCpos vhat ha hc hB hwa hvc hvB hmax)

























end ReweightedNPMLE
end

/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) :
    ∀ᵐ w ∂volume, w ∈ positiveVectors n →
      DifferentiableAt ℝ (fittedLogSelection C hCcompact hCnonempty hCpos) w := by
  obtain ⟨c, B, hc, hB, hbound⟩ := exists_uniform_positive_coordinate_bounds hCcompact hCpos
  let s : ℕ → Set (Fin n → ℝ) := fun m ↦ {w | ∀ i, 1 / ((m : ℝ) + 1) < w i}
  have hsopen : ∀ m, IsOpen (s m) := by
    intro m
    have heq : s m = ⋂ i : Fin n, {w : Fin n → ℝ | 1 / ((m : ℝ) + 1) < w i} := by
      ext w
      simp [s]
    rw [heq]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)
  have hdiff : ∀ m, ∀ᵐ w ∂volume, w ∈ s m →
      DifferentiableWithinAt ℝ (fittedLogSelection C hCcompact hCnonempty hCpos) (s m) w := by
    intro m
    have hlip := fittedLog_lipschitzOn (s := s m) hC hCpos
      (fittedValueSelection C hCcompact hCnonempty hCpos)
      (show 0 < 1 / ((m : ℝ) + 1) by positivity) hc hB
      (fun w hw i ↦ (hw i).le)
      (fun w _ i ↦ (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 i).1)
      (fun w _ i ↦ (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 i).2)
      (fun w _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos w)
    exact hlip.ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.2 hdiff] with w hw hpos
  have hsingle : ({w} : Set (Fin n → ℝ)) ⊆ positiveVectors n := by
    simpa using hpos
  obtain ⟨a, D, ha, _, hwa⟩ :=
    exists_uniform_positive_coordinate_bounds isCompact_singleton hsingle
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt ha
  have hws : w ∈ s m := fun i ↦ hm.trans_le (hwa w (mem_singleton w) i).1
  exact (hw m hws).differentiableAt ((hsopen m).mem_nhds hws)
