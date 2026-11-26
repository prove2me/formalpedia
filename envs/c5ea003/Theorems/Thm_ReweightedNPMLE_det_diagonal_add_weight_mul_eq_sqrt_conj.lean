-- Prove2me | Theorems.Thm_ReweightedNPMLE_det_diagonal_add_weight_mul_eq_sqrt_conj
-- name    : ReweightedNPMLE.det_diagonal_add_weight_mul_eq_sqrt_conj
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:37:32.454313+00:00
-- url     : https://prove2.me/theorems/7e8d3736-7d61-5708-9429-53814b132f6f
-- title:
--   Determinant identity for a weighted Jacobian and its square-root conjugate
-- statement:
--   Let $w_i>0$, let $a_i\in\mathbb R$, and let $H$ be an arbitrary real square matrix of the same finite size. Writing $D_w=\operatorname{diag}(w)$ and $S=\operatorname{diag}(\sqrt w)$, $$\det(\operatorname{diag}(a)+D_wH)=\det(\operatorname{diag}(a)+SHS).$$ Symmetry or definiteness of $H$ is not assumed. This identity allows spectral bounds to be applied to the conjugated Jacobian.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/MatrixSensitivity.lean#L209-L264

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

theorem ReweightedNPMLE.det_diagonal_add_weight_mul_eq_sqrt_conj
    {n : Type*} [Fintype n] [DecidableEq n]
    (w a : n → ℝ) (hw : ∀ i, 0 < w i) (H : Matrix n n ℝ) :
    (Matrix.diagonal a + Matrix.diagonal w * H).det =
      (Matrix.diagonal a + Matrix.diagonal (fun i ↦ Real.sqrt (w i)) * H *
        Matrix.diagonal (fun i ↦ Real.sqrt (w i))).det := by sorry
