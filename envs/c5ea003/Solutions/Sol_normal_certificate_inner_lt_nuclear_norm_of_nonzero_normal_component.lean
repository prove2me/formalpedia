-- Prove2me | solution 1 for normal_certificate_inner_lt_nuclear_norm_of_nonzero_normal_component
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T20:13:46.046363+00:00
-- url     : https://prove2.me/submissions/b53235e4-5b0e-4290-9aa7-9e6c42b56792

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Theorems.Thm_matrix_trace_duality_inequality

/-!
Reduction of node 0329f504
`normal_certificate_inner_lt_nuclear_norm_of_nonzero_normal_component`
to the trace-duality core C1 (`matrix_trace_duality_inequality`).

CR2009 Lemma 3.2 (strict form): if `‖P_{T⊥}Y‖ < 1` and `P_{T⊥}H ≠ 0` then
`⟨P_{T⊥}Y, P_{T⊥}H⟩ < ‖P_{T⊥}H‖_*`.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- F1: nuclear norm is nonnegative. -/
theorem nuclearNorm_nonneg' (X : RealMatrix n1 n2) : 0 ≤ nuclearNorm X := by
  unfold nuclearNorm
  apply Finset.sum_nonneg
  intro i _
  exact (Matrix.toEuclideanLin X).singularValues_nonneg i

/-- F2: nuclear norm is zero iff the matrix is zero. -/
theorem nuclearNorm_eq_zero_iff' (X : RealMatrix n1 n2) :
    nuclearNorm X = 0 ↔ X = 0 := by
  unfold nuclearNorm
  constructor
  · intro h
    have hzero : (Matrix.toEuclideanLin X).singularValues = 0 := by
      ext i
      by_contra hne
      have hpos : 0 < (Matrix.toEuclideanLin X).singularValues i := by
        rcases lt_or_eq_of_le ((Matrix.toEuclideanLin X).singularValues_nonneg i) with h' | h'
        · exact h'
        · exact absurd h'.symm hne
      have : (Matrix.toEuclideanLin X).singularValues i ≤
          (Matrix.toEuclideanLin X).singularValues.sum (fun _ x => x) := by
        rw [Finsupp.sum]
        by_cases hi : i ∈ (Matrix.toEuclideanLin X).singularValues.support
        · exact Finset.single_le_sum
            (fun j _ => (Matrix.toEuclideanLin X).singularValues_nonneg j) hi
        · simp only [Finsupp.mem_support_iff, not_not] at hi
          rw [hi] at hpos; exact absurd hpos (lt_irrefl 0)
      rw [h] at this
      exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl 0)
    have : Matrix.toEuclideanLin X = 0 :=
      (LinearMap.singularValues_eq_zero_iff (T := Matrix.toEuclideanLin X)).mp hzero
    have hX : Matrix.toEuclideanLin X = Matrix.toEuclideanLin 0 := by rw [this]; simp
    exact (Matrix.toEuclideanLin).injective hX
  · intro h; subst h
    simp [LinearMap.singularValues_zero]

end MatrixCompletion

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (normalProjection S Y) < 1 →
    normalProjection S H ≠ 0 →
    matrixInner (normalProjection S Y) (normalProjection S H) <
      nuclearNorm (normalProjection S H) := by
  intro hYnorm hHne
  set NY := normalProjection S Y with hNY
  set NH := normalProjection S H with hNH
  have hC1 : matrixInner NY NH ≤ spectralNorm NY * nuclearNorm NH :=
    matrix_trace_duality_inequality NY NH
  have hpos : 0 < nuclearNorm NH := by
    rcases lt_or_eq_of_le (nuclearNorm_nonneg' NH) with h | h
    · exact h
    · exact absurd ((nuclearNorm_eq_zero_iff' NH).mp h.symm) hHne
  have hstrict : spectralNorm NY * nuclearNorm NH < nuclearNorm NH := by
    calc spectralNorm NY * nuclearNorm NH < 1 * nuclearNorm NH :=
          mul_lt_mul_of_pos_right hYnorm hpos
      _ = nuclearNorm NH := one_mul _
  exact lt_of_le_of_lt hC1 hstrict
