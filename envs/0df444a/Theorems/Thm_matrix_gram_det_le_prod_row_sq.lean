-- Prove2me | Theorems.Thm_matrix_gram_det_le_prod_row_sq
-- name    : matrix_gram_det_le_prod_row_sq
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T20:15:56.049985+00:00
-- url     : https://prove2.me/theorems/b3e2d023-7cee-46f2-9cac-c969d7f658a1
-- title:
--   Gram determinant bound by squared row norms
-- statement:
--   For every finite square complex matrix, the real part of the determinant of its row Gram matrix is at most the product of its squared Euclidean row norms. The row Gram matrix is the matrix product of A and its conjugate transpose.
-- source:
--   Hadamard determinant inequality for Gram matrices

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

theorem matrix_gram_det_le_prod_row_sq {idx : Type*} [Fintype idx] [DecidableEq idx] (A : Matrix idx idx Complex) : (A * Matrix.conjTranspose A).det.re <= Finset.prod Finset.univ (fun i : idx => Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2)) := by sorry
