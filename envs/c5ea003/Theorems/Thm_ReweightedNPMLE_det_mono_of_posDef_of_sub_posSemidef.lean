-- Prove2me | Theorems.Thm_ReweightedNPMLE_det_mono_of_posDef_of_sub_posSemidef
-- name    : ReweightedNPMLE.det_mono_of_posDef_of_sub_posSemidef
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:38:32.617489+00:00
-- url     : https://prove2.me/theorems/147908b4-9940-5020-a781-1c6d0bab9db5
-- title:
--   Determinant monotonicity above a positive definite matrix
-- statement:
--   Let $A,B$ be finite real square matrices. If $A$ is symmetric positive definite and $B-A$ is symmetric positive semidefinite, then $$\det A\le\det B.$$ These hypotheses imply that $B$ is also symmetric positive definite. The result transfers a matrix lower bound into a Jacobian determinant lower bound.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/MatrixSensitivity.lean#L63-L91

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

theorem ReweightedNPMLE.det_mono_of_posDef_of_sub_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hBA : (B - A).PosSemidef) :
    A.det ≤ B.det := by sorry
