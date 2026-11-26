-- Prove2me | solution 1 for ReweightedNPMLE.projection_mulVec_dot_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:00:22.181541+00:00
-- url     : https://prove2.me/submissions/9bf3037b-6565-4b01-a78c-99f46ca31a75

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

-- Inline helpers preserved from ReweightedNPMLE.MatrixSensitivity.
section
/-!
# Determinant monotonicity for sensitivity matrices

This file supplies the positive-definite determinant comparison used in the
paper's support--sensitivity argument.  Mathlib provides the spectral theorem
and positivity of eigenvalues; the two lemmas below package them into the
Loewner monotonicity statement needed by the Jacobian estimate.
-/

open Matrix
open scoped MatrixOrder

namespace ReweightedNPMLE











/-- The quadratic form of `V Vᴴ` is the sum of the squared coordinates
against the columns of `V`. -/
theorem projectionQuadratic_eq_sum_sq
    {n k : Type*} [Fintype n] [Fintype k]
    (V : Matrix n k ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((V * Vᴴ) *ᵥ x) = ∑ j, (∑ i, V i j * x i) ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_conjTranspose]
  simp [dotProduct, vecMul, pow_two, mul_comm]



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
/-- The projection `V Vᴴ` associated with orthonormal columns is idempotent
and satisfies `⟨Px,Px⟩ = ⟨x,Px⟩`. -/
theorem solution {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq k]
    (V : Matrix n k ℝ) (hV : Vᴴ * V = 1) (x : n → ℝ) :
    let s := (V * Vᴴ) *ᵥ x
    dotProduct s s = dotProduct x s := by
  let P : Matrix n n ℝ := V * Vᴴ
  let s : n → ℝ := P *ᵥ x
  have hP2 : P * P = P := by
    dsimp [P]
    calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have hs : P *ᵥ s = s := by
    change P *ᵥ (P *ᵥ x) = P *ᵥ x
    rw [Matrix.mulVec_mulVec, hP2]
  have hVs : Vᴴ *ᵥ s = Vᴴ *ᵥ x := by
    change Vᴴ *ᵥ ((V * Vᴴ) *ᵥ x) = Vᴴ *ᵥ x
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  change dotProduct s s = dotProduct x s
  calc
    dotProduct s s = dotProduct s (P *ᵥ s) := by rw [hs]
    _ = ∑ j, (∑ i, V i j * s i) ^ 2 := by
      simpa [P] using projectionQuadratic_eq_sum_sq V s
    _ = ∑ j, (∑ i, V i j * x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      have hj := congrFun hVs j
      simpa [Matrix.mulVec, dotProduct] using hj
    _ = dotProduct x (P *ᵥ x) := by
      simpa [P] using (projectionQuadratic_eq_sum_sq V x).symm
    _ = dotProduct x s := rfl
