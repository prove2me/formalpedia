-- Prove2me | Theorems.Thm_matrix_det_norm_le_prod_row_l2
-- name    : matrix_det_norm_le_prod_row_l2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T20:02:57.74432+00:00
-- url     : https://prove2.me/theorems/417e9b4d-dd45-46dc-a98c-480d75b268fb
-- title:
--   Hadamard bound by Euclidean row norms
-- statement:
--   For every finite square complex matrix, the absolute value of its determinant is at most the product of the Euclidean norms of its rows (Hadamard determinant inequality).
-- source:
--   Hadamard determinant inequality, rowwise Euclidean norm form

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt

theorem matrix_det_norm_le_prod_row_l2 {idx : Type*} [Fintype idx] [DecidableEq idx] (A : Matrix idx idx Complex) : norm A.det <= Finset.prod Finset.univ (fun i : idx => Real.sqrt (Finset.sum Finset.univ (fun j : idx => norm (A i j) ^ 2))) := by sorry
