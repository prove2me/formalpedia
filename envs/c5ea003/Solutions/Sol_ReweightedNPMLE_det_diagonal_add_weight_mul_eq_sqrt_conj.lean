-- Prove2me | solution 1 for ReweightedNPMLE.det_diagonal_add_weight_mul_eq_sqrt_conj
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:59:23.403071+00:00
-- url     : https://prove2.me/submissions/937776a5-d447-4f07-b5a5-63e93fab5604

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Determinant monotonicity for sensitivity matrices

This file supplies the positive-definite determinant comparison used in the
paper's support--sensitivity argument.  Mathlib provides the spectral theorem
and positivity of eigenvalues; the two lemmas below package them into the
Loewner monotonicity statement needed by the Jacobian estimate.
-/

open Matrix
open scoped MatrixOrder
/-- The nonsymmetric Jacobian matrix `diag(a) + diag(w) H` has the same
determinant as its square-root conjugate
`diag(a) + diag(√w) H diag(√w)`. -/
theorem solution
    {n : Type*} [Fintype n] [DecidableEq n]
    (w a : n → ℝ) (hw : ∀ i, 0 < w i) (H : Matrix n n ℝ) :
    (Matrix.diagonal a + Matrix.diagonal w * H).det =
      (Matrix.diagonal a + Matrix.diagonal (fun i ↦ Real.sqrt (w i)) * H *
        Matrix.diagonal (fun i ↦ Real.sqrt (w i))).det := by
  let s : n → ℝ := fun i ↦ Real.sqrt (w i)
  let S : Matrix n n ℝ := Matrix.diagonal s
  have hdiagMul (x y : n → ℝ) :
      Matrix.diagonal x * Matrix.diagonal y = Matrix.diagonal (fun i ↦ x i * y i) := by
    classical
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    · intro b hb hbi
      simp [Ne.symm hbi]
    · simp
  have hSsq : S * S = Matrix.diagonal w := by
    change Matrix.diagonal s * Matrix.diagonal s = Matrix.diagonal w
    rw [hdiagMul]
    congr 1
    funext i
    dsimp [s]
    nlinarith [Real.sq_sqrt (hw i).le]
  have hAS : Matrix.diagonal a * S = S * Matrix.diagonal a := by
    change Matrix.diagonal a * Matrix.diagonal s =
      Matrix.diagonal s * Matrix.diagonal a
    rw [hdiagMul, hdiagMul]
    congr 1
    funext i
    ring
  have hmul : (Matrix.diagonal a + Matrix.diagonal w * H) * S =
      S * (Matrix.diagonal a + S * H * S) := by
    rw [← hSsq]
    calc
      (Matrix.diagonal a + S * S * H) * S =
          Matrix.diagonal a * S + S * S * H * S := by rw [Matrix.add_mul]
      _ = S * Matrix.diagonal a + S * S * H * S := by rw [hAS]
      _ = S * (Matrix.diagonal a + S * H * S) := by noncomm_ring
  have hSdet : 0 < S.det := by
    change 0 < (Matrix.diagonal s).det
    rw [Matrix.det_diagonal]
    exact Finset.prod_pos fun i _ ↦ Real.sqrt_pos.2 (hw i)
  have hdet := congrArg Matrix.det hmul
  simp only [Matrix.det_mul] at hdet
  apply mul_right_cancel₀ hSdet.ne'
  calc
    (Matrix.diagonal a + Matrix.diagonal w * H).det * S.det =
        S.det * (Matrix.diagonal a + S * H * S).det := hdet
    _ = (Matrix.diagonal a + S * H * S).det * S.det := mul_comm _ _
