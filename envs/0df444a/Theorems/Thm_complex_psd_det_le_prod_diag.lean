-- Prove2me | Theorems.Thm_complex_psd_det_le_prod_diag
-- name    : complex_psd_det_le_prod_diag
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T21:40:42.971238+00:00
-- url     : https://prove2.me/theorems/77ff8c8c-b142-4c28-90de-3c949a05bd48
-- title:
--   Hadamard bound for positive semidefinite complex matrices
-- statement:
--   For a finite Hermitian positive semidefinite complex matrix, the determinant is real and nonnegative, and it is at most the product of the real diagonal entries. This is the Hadamard determinant inequality in its positive semidefinite matrix form.
-- source:
--   Hadamard determinant inequality, Gram matrix formulation; https://en.wikipedia.org/wiki/Hadamard%27s_inequality. The target theorem cites this inequality applied to the columns of A.

import Mathlib.Analysis.Matrix.PosDef
open scoped ComplexOrder

theorem complex_psd_det_le_prod_diag {idx : Type*} [Fintype idx] [DecidableEq idx] (B : Matrix idx idx Complex) (hB : B.PosSemidef) : B.det.re <= Finset.prod Finset.univ (fun i : idx => (B i i).re) := by sorry
