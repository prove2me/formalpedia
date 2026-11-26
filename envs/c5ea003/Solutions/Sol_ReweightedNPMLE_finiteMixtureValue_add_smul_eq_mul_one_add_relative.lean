-- Prove2me | solution 1 for ReweightedNPMLE.finiteMixtureValue_add_smul_eq_mul_one_add_relative
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:59:31.640782+00:00
-- url     : https://prove2.me/submissions/98cba005-1faa-4e8b-88b7-b738fa5d9fa8

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
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
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The fitted-value change produced by an affine coefficient perturbation is
the multiplicative relative-dictionary path. -/
theorem solution
    {k n : ℕ} (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ)
    (p : Fin k → ℝ) (hpv : finiteMixtureValue A p = v)
    (hv : ∀ i, v i ≠ 0) (c : Fin k → ℝ) (t : ℝ) :
    finiteMixtureValue A (p + t • c) =
      fun i ↦ v i * (1 + t * relativeDictionaryMap A v c i) := by
  funext i
  have hpvi := congrFun hpv i
  unfold finiteMixtureValue at hpvi ⊢
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    relativeDictionaryMap_apply] at hpvi ⊢
  have hexpand : (∑ x, (p x + t * c x) * A x i) =
      (∑ x, p x * A x i) + t * ∑ x, c x * A x i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand, hpvi]
  field_simp [hv i]
