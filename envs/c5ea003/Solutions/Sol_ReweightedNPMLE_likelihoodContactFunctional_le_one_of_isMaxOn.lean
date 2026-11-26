-- Prove2me | solution 1 for ReweightedNPMLE.likelihoodContactFunctional_le_one_of_isMaxOn
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:59:15.485848+00:00
-- url     : https://prove2.me/submissions/17428181-7943-4868-89b9-388cbc40a8d0

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_likelihoodContactNumerator_le_total_of_isMaxOn

-- Inline helpers preserved from ReweightedNPMLE.Weights.
section
/-!
# Weighted likelihood and normalization

This file formalizes the deterministic normalization statements in Section 2.2 of the
paper.  Vectors are represented by functions on `Fin n`; this is the representation used
throughout the rest of the development.
-/

open scoped BigOperators

namespace ReweightedNPMLE























theorem total_pos {n : ℕ} [Nonempty (Fin n)] {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) : 0 < total w := by
  classical
  exact Finset.sum_pos (fun i _ ↦ hw i) Finset.univ_nonempty





















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FittedContact.
section
/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE




  


@[simp] theorem likelihoodContactFunctional_apply {n : ℕ}
    (w v a : Fin n → ℝ) :
    likelihoodContactFunctional w v a =
      ∑ i, w i / (v i * total w) * a i := by
  simp [likelihoodContactFunctional]











end ReweightedNPMLE
end

/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Every feasible vector lies below the contact hyperplane at a positive
weighted maximizer. -/
theorem solution
    {n : ℕ} [Nonempty (Fin n)] {C : Set (Fin n → ℝ)}
    (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (w v a : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) (ha : a ∈ C) :
    likelihoodContactFunctional w v a ≤ 1 := by
  have hvpos := hCpos hvmax.1
  have hraw := likelihoodContactNumerator_le_total_of_isMaxOn
    hC hCpos w v a hvmax ha
  have hrewrite : likelihoodContactFunctional w v a =
      likelihoodContactNumerator w v a / total w := by
    rw [likelihoodContactFunctional_apply]
    unfold likelihoodContactNumerator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hvpos i).ne', (total_pos hw).ne']
  rw [hrewrite, div_le_one (total_pos hw)]
  exact hraw
