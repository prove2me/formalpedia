-- Prove2me | solution 1 for spectral_norm_pow_two_mul_le_trace_pow
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T15:52:38.25357+00:00
-- url     : https://prove2.me/submissions/b49cbf8f-8c67-4093-8167-fca87da7735f

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian

open scoped Matrix.Norms.L2Operator
open Matrix MatrixCompletion

theorem solution
    {d : ℕ} (hd0 : 0 < d) (X : Matrix (Fin d) (Fin d) ℝ) (hX : X.IsHermitian) (p : ℕ) :
    spectralNorm X ^ (2 * p) ≤ Matrix.trace (X ^ (2 * p)) := by
  classical
  set ev := hX.eigenvalues with hev
  have hnorm : spectralNorm X = ‖ev‖ := by
    have hsp : spectralNorm X = ‖X‖ := (Matrix.l2_opNorm_def X).symm
    rw [hsp]
    conv_lhs => rw [hX.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
    congr 1
  have htrace : Matrix.trace (X ^ (2 * p)) = ∑ i, (ev i) ^ (2 * p) := by
    set U := hX.eigenvectorUnitary
    set D : Matrix (Fin d) (Fin d) ℝ := diagonal (RCLike.ofReal ∘ ev) with hD
    have hXpow : X ^ (2 * p) = (U : Matrix (Fin d) (Fin d) ℝ) * D ^ (2 * p) *
        (star U : Matrix (Fin d) (Fin d) ℝ) := by
      conv_lhs => rw [hX.spectral_theorem]
      rw [← map_pow, Unitary.conjStarAlgAut_apply]
    rw [hXpow, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
    rw [hD, diagonal_pow, Matrix.trace_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hnorm, htrace]
  have hne : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  obtain ⟨j, hjmax⟩ := Finite.exists_max (fun i => |ev i|)
  have hj : ‖ev‖ = |ev j| := by
    refine le_antisymm ?_ ?_
    · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr (fun i => by
        simpa [Real.norm_eq_abs] using hjmax i)
    · simpa [Real.norm_eq_abs] using norm_le_pi_norm ev j
  rw [hj]
  have hpow : |ev j| ^ (2 * p) = (ev j) ^ (2 * p) := by
    rw [pow_mul, pow_mul, sq_abs]
  rw [hpow]
  refine Finset.single_le_sum (f := fun i => (ev i) ^ (2 * p)) (fun i _ => ?_)
    (Finset.mem_univ j)
  show 0 ≤ (ev i) ^ (2 * p)
  rw [pow_mul]
  positivity

#print axioms solution
