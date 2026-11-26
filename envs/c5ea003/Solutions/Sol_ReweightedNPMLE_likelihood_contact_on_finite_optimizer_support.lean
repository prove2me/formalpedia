-- Prove2me | solution 1 for ReweightedNPMLE.likelihood_contact_on_finite_optimizer_support
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:59:55.996618+00:00
-- url     : https://prove2.me/submissions/ffa5fc6c-90c9-49d7-8080-87844b12f55d

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
import Theorems.Thm_ReweightedNPMLE_contact_eq_one_on_coefficientSupport
import Theorems.Thm_ReweightedNPMLE_likelihoodContactFunctional_le_one_of_isMaxOn

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

theorem total_ne_zero {n : ℕ} [Nonempty (Fin n)] {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) : total w ≠ 0 :=
  (total_pos hw).ne'



















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

/-- The fitted vector itself lies on the normalized contact hyperplane. -/
theorem likelihoodContactFunctional_self {n : ℕ} [Nonempty (Fin n)]
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) :
    likelihoodContactFunctional w v v = 1 := by
  rw [likelihoodContactFunctional_apply]
  calc
    (∑ i, w i / (v i * total w) * v i) =
        ∑ i, w i / total w := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hv i).ne', (total_pos hw).ne']
    _ = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, total]
      exact mul_inv_cancel₀ (total_ne_zero hw)









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
/-- For a finite dictionary, every active atom of an optimizing mixture lies
on the likelihood contact hyperplane. -/
theorem solution
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Fin m → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin m → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v) :
    ∀ j ∈ coefficientSupport p,
      likelihoodContactFunctional w v (A j) = 1 := by
  apply contact_eq_one_on_coefficientSupport A v p
    (likelihoodContactFunctional w v) hp
  · exact likelihoodContactFunctional_self w v hw hvpos
  · intro j
    apply likelihoodContactFunctional_le_one_of_isMaxOn
      (convex_convexHull ℝ (Set.range A))
      _ w v (A j) hw hvmax
        (subset_convexHull ℝ (Set.range A) (Set.mem_range_self j))
    exact convexHull_min (fun a ha i ↦ by
      rcases ha with ⟨j, rfl⟩
      exact hApos j i) (convex_positiveVectors n)
