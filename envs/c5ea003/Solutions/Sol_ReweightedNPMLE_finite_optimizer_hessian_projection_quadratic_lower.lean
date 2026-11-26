-- Prove2me | solution 1 for ReweightedNPMLE.finite_optimizer_hessian_projection_quadratic_lower
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:04:14.223789+00:00
-- url     : https://prove2.me/submissions/ee0095fe-727a-49fd-987e-3f48b3a23e0e

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
import Theorems.Thm_ReweightedNPMLE_finite_optimizer_directional_sensitivity_lower
import Theorems.Thm_ReweightedNPMLE_projection_mulVec_dot_self_eq
import Theorems.Thm_ReweightedNPMLE_submodule_projection_mulVec_mem

-- Inline helpers preserved from ReweightedNPMLE.FittedHessian.
section
/-!
# Hessian structure of the fitted likelihood value

This file turns the envelope identity into the analytic Hessian facts used by
the paper.  The derivative of the fitted log-vector induces the second
derivative of the optimized value.  Mathlib's second-derivative symmetry
theorem makes its matrix Hermitian, while monotonicity of fitted logs makes
its quadratic form nonnegative.  Thus, at every differentiability point, the
matrix representing the fitted-log derivative is positive semidefinite.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE



























@[simp] theorem fittedLogDerivativeMatrix_mulVec {n : ℕ}
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (h : Fin n → ℝ) :
    fittedLogDerivativeMatrix J *ᵥ h = J h := by
  exact LinearMap.toMatrix'_mulVec J.toLinearMap h









end ReweightedNPMLE
end

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











































theorem submoduleOrthonormalMatrix_conjTranspose_mul {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    (submoduleOrthonormalMatrix S)ᴴ * submoduleOrthonormalMatrix S = 1 := by
  classical
  ext j l
  rw [Matrix.mul_apply]
  change (∑ i, ((stdOrthonormalBasis ℝ S j : S) : Fin n → ℝ) i *
      ((stdOrthonormalBasis ℝ S l : S) : Fin n → ℝ) i) = _
  simp_rw [← Real.inner_apply]
  rw [← PiLp.inner_apply]
  change inner ℝ (stdOrthonormalBasis ℝ S j) (stdOrthonormalBasis ℝ S l) = _
  exact (orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ S).orthonormal j l).trans
    (by simp [Matrix.one_apply])





















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
/-- Coordinatewise quadratic lower bound of the conjugated fitted-log
Hessian by the active tangent projection. -/
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
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w)
    (x : Fin n → ℝ) :
    let S := weightedRelativeTangentSpace A v w
    let V := submoduleOrthonormalMatrix S
    let R := Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
      fittedLogDerivativeMatrix J *
      Matrix.diagonal (fun i ↦ Real.sqrt (w i))
    (∑ j, (∑ i, V i j * x i) ^ 2) ≤ dotProduct x (R *ᵥ x) := by
  let S := weightedRelativeTangentSpace A v w
  let V := submoduleOrthonormalMatrix S
  let D : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i ↦ Real.sqrt (w i))
  let R : Matrix (Fin n) (Fin n) ℝ := D * fittedLogDerivativeMatrix J * D
  let s : Fin n → ℝ := (V * Vᴴ) *ᵥ x
  have hsmem : WithLp.toLp 2 s ∈ S := by
    exact submodule_projection_mulVec_mem S x
  rcases hsmem with ⟨c, hc⟩
  let u : Fin n → ℝ := relativeDictionaryMap A v c.1
  have hsu (i : Fin n) : Real.sqrt (w i) * u i = s i := by
    have hi := congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y i) hc
    simpa [S, weightedRelativeTangentSpace,
      weightedMassPreservingRelativeMap, weightedRelativeDictionaryMap,
      u, s] using hi
  let h : Fin n → ℝ := fun i ↦ Real.sqrt (w i) * x i
  have hdir := finite_optimizer_directional_sensitivity_lower
    A v p w hw hp hpfull hvpos hApos vhat hC hA hmax hvw hpsi hz h c
  have hcross : (∑ i, h i * u i) = dotProduct x s := by
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [h]
    rw [← hsu i]
    ring
  have hnorm : (∑ i, w i * u i ^ 2) = dotProduct s s := by
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hsu i]
    nlinarith [Real.sq_sqrt (hw i).le]
  have hproj : dotProduct s s = dotProduct x s := by
    exact projection_mulVec_dot_self_eq V
      (submoduleOrthonormalMatrix_conjTranspose_mul S) x
  have hdiag : D *ᵥ x = h := by
    funext i
    exact Matrix.mulVec_diagonal _ _ _
  have hRmul : R *ᵥ x = fun i ↦ Real.sqrt (w i) * J h i := by
    calc
      R *ᵥ x = D *ᵥ (fittedLogDerivativeMatrix J *ᵥ (D *ᵥ x)) := by
        dsimp [R]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = D *ᵥ (J h) := by rw [hdiag, fittedLogDerivativeMatrix_mulVec]
      _ = fun i ↦ Real.sqrt (w i) * J h i := by
        funext i
        exact Matrix.mulVec_diagonal _ _ _
  have hrhs : (∑ i, h i * J h i) = dotProduct x (R *ᵥ x) := by
    rw [hRmul, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [h]
    ring
  change (∑ j, (∑ i, V i j * x i) ^ 2) ≤ dotProduct x (R *ᵥ x)
  calc
    (∑ j, (∑ i, V i j * x i) ^ 2) = dotProduct x s := by
      simpa [s] using (projectionQuadratic_eq_sum_sq V x).symm
    _ = 2 * dotProduct x s - dotProduct s s := by rw [hproj]; ring
    _ = 2 * ∑ i, h i * u i - ∑ i, w i * u i ^ 2 := by
      rw [hcross, hnorm]
    _ ≤ ∑ i, h i * J h i := hdir
    _ = dotProduct x (R *ᵥ x) := hrhs
