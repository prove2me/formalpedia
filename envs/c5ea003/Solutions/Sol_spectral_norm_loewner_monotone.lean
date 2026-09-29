-- Prove2me | solution 1 for spectral_norm_loewner_monotone
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T17:17:08.0499+00:00
-- url     : https://prove2.me/submissions/f6e36b6b-0b1b-4625-a15e-f2daeeda1ab1

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

open scoped Matrix RealInnerProductSpace BigOperators
open RCLike ContinuousLinearMap

theorem solution {n : Nat} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hBA : (B - A).PosSemidef) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ := by
  set Ta := Matrix.toEuclideanCLM (𝕜 := ℝ) A with hTa
  set Tb := Matrix.toEuclideanCLM (𝕜 := ℝ) B with hTb
  -- `toEuclideanCLM A` is self-adjoint since A is Hermitian.
  have hsymTa : (Ta : EuclideanSpace ℝ (Fin n) →L[ℝ] _).IsSymmetric := by
    have hstar : star (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
        = Matrix.toEuclideanCLM (𝕜 := ℝ) (star A) :=
      (Matrix.toEuclideanCLM (𝕜 := ℝ)).map_star' A |>.symm
    have hsa : IsSelfAdjoint Ta := by
      rw [hTa, IsSelfAdjoint, hstar]
      exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ)) hA.1.eq
    exact hsa.isSymmetric
  -- Rayleigh-quotient identity.
  have hrayl : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)),
      (Matrix.toEuclideanCLM (𝕜 := ℝ) X).rayleighQuotient x
        = (x ⬝ᵥ X *ᵥ x) / ‖x‖ ^ 2 := by
    intro X x
    rw [rayleighQuotient, reApplyInnerSelf_apply]
    have hinner : (inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) X x) x : ℝ) = x ⬝ᵥ X *ᵥ x := by
      rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
    rw [hinner]; simp
  -- Norm of a symmetric operator = sup of |Rayleigh|.
  rw [Ta.norm_eq_iSup_rayleighQuotient hsymTa]
  apply ciSup_le
  intro x
  have hraylA : (Ta.rayleighQuotient x) = (x ⬝ᵥ A *ᵥ x) / ‖x‖ ^ 2 := by
    rw [hTa]; exact hrayl A x
  have hraylB : (Tb.rayleighQuotient x) = (x ⬝ᵥ B *ᵥ x) / ‖x‖ ^ 2 := by
    rw [hTb]; exact hrayl B x
  have hxA : 0 ≤ x ⬝ᵥ A *ᵥ x := by
    have := hA.re_dotProduct_nonneg x; simpa using this
  have hAB : x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x := by
    have hxBA : 0 ≤ x ⬝ᵥ (B - A) *ᵥ x := by
      have := hBA.re_dotProduct_nonneg x; simpa using this
    have hsplit : x ⬝ᵥ B *ᵥ x = x ⬝ᵥ A *ᵥ x + x ⬝ᵥ (B - A) *ᵥ x := by
      rw [Matrix.sub_mulVec, dotProduct_sub]; ring
    rw [hsplit]; linarith
  have hraylA_nonneg : 0 ≤ Ta.rayleighQuotient x := by rw [hraylA]; positivity
  rw [abs_of_nonneg hraylA_nonneg]
  calc Ta.rayleighQuotient x
      ≤ Tb.rayleighQuotient x := by rw [hraylA, hraylB]; gcongr
    _ ≤ |Tb.rayleighQuotient x| := le_abs_self _
    _ ≤ ‖Tb‖ := Tb.rayleighQuotient_le_norm x

#print axioms solution
