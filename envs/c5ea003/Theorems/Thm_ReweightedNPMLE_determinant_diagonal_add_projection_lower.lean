-- Prove2me | Theorems.Thm_ReweightedNPMLE_determinant_diagonal_add_projection_lower
-- name    : ReweightedNPMLE.determinant_diagonal_add_projection_lower
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:02.172221+00:00
-- url     : https://prove2.me/theorems/b9bc2659-ec8d-40af-8e0d-f01a874806b1
-- title:
--   Quantitative determinant gain from orthonormal sensitivity directions
-- statement:
--   Let $a_1,\ldots,a_n$ satisfy $0<a_i\le9/8$, and let $V\in\mathbb R^{n\times k}$ have orthonormal columns, $V^\mathsf TV=I_k$. Then $$\det(\operatorname{diag}(a)+VV^\mathsf T)\ge\left(\prod_{i=1}^n a_i\right)(17/9)^k.$$ This gives a fixed determinant gain per independent sensitivity direction.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/MatrixSensitivity.lean#L93-L187

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

theorem ReweightedNPMLE.determinant_diagonal_add_projection_lower
    {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (a : n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8)
    (V : Matrix n k ℝ) (hV : Vᴴ * V = 1) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ Fintype.card k ≤
      (diagonal a + V * Vᴴ).det := by sorry
