-- Prove2me | solution 1 for ReweightedNPMLE.relativeDictionary_weighted_sum_eq_zero_of_contact
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:00:16.705743+00:00
-- url     : https://prove2.me/submissions/4f4e410c-011b-48fd-a17a-fa9efeaf9387

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

-- Inline helpers preserved from ReweightedNPMLE.SupportSensitivity.
section
/-!
# Finite-support tangent directions

This file formalizes the algebraic half of the paper's matrix-sensitivity
lemma.  Mass-preserving perturbations of a `k`-atom optimizer form a
`(k - 1)`-dimensional coefficient space.  A linearly independent evaluation
dictionary maps that space injectively to relative fitted-value directions.
After the square-root weight scaling, these directions remain
`(k - 1)`-dimensional, are orthogonal to the square-root weight vector by the
likelihood contact equations, and admit an explicit orthonormal matrix.
-/

open Set
open scoped BigOperators Matrix

namespace ReweightedNPMLE















@[simp] theorem relativeDictionaryMap_apply {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (c : Fin k → ℝ) (i : Fin n) :
    relativeDictionaryMap A v c i = (∑ j, c j * A j i) / v i := rfl

















































end ReweightedNPMLE
end

/-!
# Finite-support tangent directions

This file formalizes the algebraic half of the paper's matrix-sensitivity
lemma.  Mass-preserving perturbations of a `k`-atom optimizer form a
`(k - 1)`-dimensional coefficient space.  A linearly independent evaluation
dictionary maps that space injectively to relative fitted-value directions.
After the square-root weight scaling, these directions remain
`(k - 1)`-dimensional, are orthogonal to the square-root weight vector by the
likelihood contact equations, and admit an explicit orthonormal matrix.
-/

open Set
open scoped BigOperators Matrix

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ)
    (hcontact : ∀ j, ∑ i, w i * (A j i / v i) = total w)
    (c : zeroSumCoefficients k) :
    ∑ i, w i * relativeDictionaryMap A v c i = 0 := by
  classical
  calc
    (∑ i, w i * relativeDictionaryMap A v c i) =
        ∑ i, ∑ j, c.1 j * (w i * (A j i / v i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [relativeDictionaryMap_apply]
      simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, c.1 j * ∑ i, w i * (A j i / v i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ j, c.1 j * total w := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcontact j]
    _ = 0 := by
      have hc : ∑ j, c.1 j = 0 := by
        have hc' := c.property
        change coefficientTotalLinearMap k c.1 = 0 at hc'
        exact hc'
      rw [← Finset.sum_mul, hc]
      simp
