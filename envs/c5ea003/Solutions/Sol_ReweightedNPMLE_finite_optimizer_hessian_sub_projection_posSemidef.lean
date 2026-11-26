-- Prove2me | solution 1 for ReweightedNPMLE.finite_optimizer_hessian_sub_projection_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:05:06.644084+00:00
-- url     : https://prove2.me/submissions/c27c9554-42f2-4868-9240-24df853dc97d

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
import Theorems.Thm_ReweightedNPMLE_finite_optimizer_hessian_projection_quadratic_lower
import Theorems.Thm_ReweightedNPMLE_fittedLogDerivativeMatrix_isHermitian_of_eventually

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

/-- A coordinatewise quadratic lower bound by the columns of `V` is
equivalent to Loewner domination of the projection-shaped matrix `V Vᴴ`.
This packages the final linear-algebra step of the support-sensitivity
argument. -/
theorem matrix_sub_projection_posSemidef_of_quadratic_lower
    {n k : Type*} [Fintype n] [Fintype k]
    (R : Matrix n n ℝ) (hR : R.IsHermitian)
    (V : Matrix n k ℝ)
    (hquad : ∀ x : n → ℝ,
      (∑ j, (∑ i, V i j * x i) ^ 2) ≤ x ⬝ᵥ (R *ᵥ x)) :
    (R - V * Vᴴ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact hR.sub (Matrix.isHermitian_mul_conjTranspose_self V)
  · intro x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    rw [projectionQuadratic_eq_sum_sq]
    exact sub_nonneg.mpr (hquad x)

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
/-- Loewner domination of the active-support tangent projection by the
square-root-conjugated fitted-log Hessian. -/
theorem solution
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w) :
    let S := weightedRelativeTangentSpace A v w
    let V := submoduleOrthonormalMatrix S
    let R := Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
      fittedLogDerivativeMatrix J *
      Matrix.diagonal (fun i ↦ Real.sqrt (w i))
    (R - V * Vᴴ).PosSemidef := by
  let S := weightedRelativeTangentSpace A v w
  let V := submoduleOrthonormalMatrix S
  let D : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i ↦ Real.sqrt (w i))
  let R : Matrix (Fin n) (Fin n) ℝ := D * fittedLogDerivativeMatrix J * D
  have hJ : (fittedLogDerivativeMatrix J).IsHermitian :=
    fittedLogDerivativeMatrix_isHermitian_of_eventually (fittedOptimalValue vhat)
      (fun q i ↦ Real.log (vhat q i)) hpsi hz
  have hD : D.IsHermitian := by
    exact Matrix.isHermitian_diagonal _
  have hR : R.IsHermitian := by
    have hc := Matrix.isHermitian_conjTranspose_mul_mul D hJ
    rw [hD.eq] at hc
    exact hc
  apply matrix_sub_projection_posSemidef_of_quadratic_lower R hR V
  intro x
  exact finite_optimizer_hessian_projection_quadratic_lower
    A v p w hw hp hpfull hvpos hApos vhat hC hA hmax hvw hpsi hz x
