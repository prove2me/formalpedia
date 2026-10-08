-- Prove2me | Theorems.Thm_complex_gram_det_le_prod_col_sq
-- name    : complex_gram_det_le_prod_col_sq
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T20:50:44.602806+00:00
-- url     : https://prove2.me/theorems/6ae14207-b366-4778-9acd-336fb2667392
-- title:
--   Hadamard bound for complex Gram determinants
-- statement:
--   For every finite square complex matrix A, the determinant of A? A is bounded above by the product of the squared Euclidean norms of the columns of A.
-- source:
--   Hadamard determinant inequality applied to the columns of a complex matrix.

import Mathlib.Analysis.Matrix.PosDef
open scoped ComplexOrder

theorem complex_gram_det_le_prod_col_sq {idx : Type*} [Fintype idx] [DecidableEq idx]
    (A : Matrix idx idx Complex) :
    (Matrix.conjTranspose A * A).det.re <=
      Finset.prod Finset.univ (fun i : idx =>
        Finset.sum Finset.univ (fun j : idx => norm (A j i) ^ 2)) := by sorry
