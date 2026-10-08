-- Prove2me | Theorems.Thm_complex_posSemidef_eq_gram
-- name    : complex_posSemidef_eq_gram
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-07T20:50:58.127964+00:00
-- url     : https://prove2.me/theorems/7579aa0f-f4f5-425a-b223-ebcb7316ac15
-- title:
--   Gram factorization of positive semidefinite complex matrices
-- statement:
--   Every finite positive semidefinite complex matrix M is a Gram matrix: some complex matrix A satisfies M = A? A.
-- source:
--   Positive square root factorization for positive semidefinite matrices.

import Mathlib.Analysis.Matrix.PosDef
open scoped ComplexOrder

theorem complex_posSemidef_eq_gram {idx : Type*} [Fintype idx] [DecidableEq idx]
    (M : Matrix idx idx Complex) (hM : M.PosSemidef) :
    Exists fun A : Matrix idx idx Complex => M = Matrix.conjTranspose A * A := by sorry
