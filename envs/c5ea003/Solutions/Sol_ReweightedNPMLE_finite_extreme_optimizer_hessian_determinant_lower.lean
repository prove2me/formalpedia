-- Prove2me | solution 1 for ReweightedNPMLE.finite_extreme_optimizer_hessian_determinant_lower
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:06:14.604595+00:00
-- url     : https://prove2.me/submissions/e29e3fdb-40a0-4a74-87f2-9530f7e5a470

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
import Theorems.Thm_ReweightedNPMLE_det_mono_of_posDef_of_sub_posSemidef
import Theorems.Thm_ReweightedNPMLE_determinant_diagonal_add_projection_lower
import Theorems.Thm_ReweightedNPMLE_finite_extreme_optimizer_weighted_tangent_finrank
import Theorems.Thm_ReweightedNPMLE_finite_optimizer_hessian_sub_projection_posSemidef

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







/-- Matrix-sensitivity form of the Jacobian lower bound.  If `R` dominates
the orthogonal projection `V Vᴴ`, its determinant is at least the same
`(17/9)^k` gain over the diagonal factor. -/
theorem determinant_diagonal_add_psd_projection_lower
    {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (a : n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8)
    (V : Matrix n k ℝ) (hV : Vᴴ * V = 1) (R : Matrix n n ℝ)
    (hR : (R - V * Vᴴ).PosSemidef) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ Fintype.card k ≤
      (diagonal a + R).det := by
  have hbase : (diagonal a + V * Vᴴ).PosDef :=
    (Matrix.PosDef.diagonal ha0).add_posSemidef
      (Matrix.posSemidef_self_mul_conjTranspose V)
  have hsub : ((diagonal a + R) - (diagonal a + V * Vᴴ)).PosSemidef := by
    have heq : (diagonal a + R) - (diagonal a + V * Vᴴ) = R - V * Vᴴ := by abel
    rwa [heq]
  exact (determinant_diagonal_add_projection_lower a ha0 haUpper V hV).trans
    (det_mono_of_posDef_of_sub_posSemidef hbase hsub)







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

-- Inline helpers preserved from ReweightedNPMLE.SupportSensitivityAnalytic.
section
/-!
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE



/-- A finite convex combination of dictionary atoms lies in their convex
hull. -/
theorem finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex
    {k : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin k → E) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k) :
    finiteMixtureValue A p ∈ convexHull ℝ (Set.range A) := by
  apply (convex_convexHull ℝ (Set.range A)).sum_mem (fun i _ ↦ hp.1 i) hp.2
  intro i _
  exact subset_convexHull ℝ (Set.range A) ⟨i, rfl⟩

























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
/-- A `k`-atom extreme optimizer contributes the exact `(17/9)^(k-1)`
determinant gain in the paper's matrix-sensitivity lemma. -/
theorem solution
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hextreme : p ∈ (finiteMixtureFiber A v).extremePoints ℝ)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ (k - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
        fittedLogDerivativeMatrix J *
        Matrix.diagonal (fun i ↦ Real.sqrt (w i))).det := by
  let S := weightedRelativeTangentSpace A v w
  let V := submoduleOrthonormalMatrix S
  let R := Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
    fittedLogDerivativeMatrix J * Matrix.diagonal (fun i ↦ Real.sqrt (w i))
  have hprojection : (R - V * Vᴴ).PosSemidef :=
    finite_optimizer_hessian_sub_projection_posSemidef
      A v p w hw hp hpfull hvpos hApos vhat hC hA hmax hvw hpsi hz
  have hsubset : convexHull ℝ (Set.range A) ⊆ C := convexHull_min hA hC
  have hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v := by
    refine ⟨?_, ?_⟩
    · rw [← hp.2]
      exact finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex A p hp.1
    · intro q hq
      simpa [hvw] using (hmax w).2 q (hsubset hq)
  have hdim : Module.finrank ℝ S = k - 1 :=
    finite_extreme_optimizer_weighted_tangent_finrank
      A v p w hw hp hpfull hvpos hApos hvmax hextreme
  have hdet := determinant_diagonal_add_psd_projection_lower a ha0 haUpper
    V (submoduleOrthonormalMatrix_conjTranspose_mul S) R hprojection
  simpa only [Fintype.card_fin, hdim] using hdet
