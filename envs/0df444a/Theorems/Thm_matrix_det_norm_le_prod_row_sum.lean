-- Prove2me | Theorems.Thm_matrix_det_norm_le_prod_row_sum
-- name    : matrix_det_norm_le_prod_row_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-07T19:49:27.96284+00:00
-- url     : https://prove2.me/theorems/84aa3fa2-09a3-4b89-af10-e9e55edca8af
-- title:
--   Determinant bounded by the product of row sums
-- statement:
--   For every finite square complex matrix, the absolute value of its determinant is at most the product of the sums of absolute values along its rows. This reusable estimate controls determinants from rowwise bounds.
-- source:
--   Hadamard determinant inequality; follows from the Leibniz expansion.

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

theorem matrix_det_norm_le_prod_row_sum
    {idx : Type*} [Fintype idx] [DecidableEq idx] (A : Matrix idx idx Complex) :
    norm A.det <= Finset.prod Finset.univ (fun i : idx =>
      Finset.sum Finset.univ (fun j : idx => norm (A i j))) := by sorry
