-- Prove2me | Theorems.Thm_ReweightedNPMLE_det_one_add_posSemidef_ge_one
-- name    : ReweightedNPMLE.det_one_add_posSemidef_ge_one
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:37:56.845588+00:00
-- url     : https://prove2.me/theorems/0040727e-3c5d-47e3-bcff-06dd76ed0682
-- title:
--   Determinant lower bound after adding a positive semidefinite matrix
-- statement:
--   For every finite real symmetric positive semidefinite matrix $C$, $$\det(I+C)\ge1.$$ The statement includes zero-dimensional matrices. This is the base determinant inequality used to prove monotonicity in Loewner order.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/MatrixSensitivity.lean#L19-L61

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

theorem ReweightedNPMLE.det_one_add_posSemidef_ge_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℝ} (hC : C.PosSemidef) :
    1 ≤ (1 + C).det := by sorry
