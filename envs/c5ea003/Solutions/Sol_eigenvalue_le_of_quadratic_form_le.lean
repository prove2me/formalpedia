-- Prove2me | solution 1 for eigenvalue_le_of_quadratic_form_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T02:33:21.280097+00:00
-- url     : https://prove2.me/submissions/a79bb71b-d550-400d-b6db-22c8f2f6a8cd

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Mul

open Matrix
open scoped BigOperators

theorem solution {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (normV : ℝ)
    (hquad : ∀ v : Fin d → ℝ, (star v ⬝ᵥ A *ᵥ v) ≤ normV * (star v ⬝ᵥ v))
    (i : Fin d) :
    hA.eigenvalues i ≤ normV := by
  classical
  set v : Fin d → ℝ := ⇑(hA.eigenvectorBasis i) with hv
  have hev : A *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
  have hunit : (star v ⬝ᵥ v) = 1 := by
    have ho := hA.eigenvectorBasis.orthonormal.1 i
    have hstar : (star v ⬝ᵥ v) = ∑ k, v k * v k := by
      simp [dotProduct, Pi.star_apply, star_trivial, mul_comm]
    rw [hstar]
    have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := ho
    have hsq : ‖hA.eigenvectorBasis i‖ ^ 2 = ∑ k, v k * v k := by
      rw [EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt (by positivity)]
      congr 1; funext k; rw [hv]; simp [Real.norm_eq_abs, sq_abs, pow_two]
    rw [← hsq, hnorm]; norm_num
  have hqf : (star v ⬝ᵥ A *ᵥ v) = hA.eigenvalues i := by
    rw [hev, dotProduct_smul, smul_eq_mul, hunit, mul_one]
  have hb := hquad v
  rw [hqf, hunit, mul_one] at hb
  exact hb
