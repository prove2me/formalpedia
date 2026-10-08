-- Prove2me | Theorems.Thm_BookSixth_jacobi_reduction
-- name    : BookSixth.jacobi_reduction
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:36:05.871709+00:00
-- url     : https://prove2.me/theorems/6c109bb7-ebc3-46c4-84d6-70e4aab50cfb
-- title:
--   Chapter 7, Jacobi reduction lemma
-- statement:
--   If a real symmetric matrix has positive sum of squared off-diagonal entries, an orthogonal conjugation strictly decreases this sum.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 7, Jacobi reduction lemma, p. 40. https://doi.org/10.1007/978-3-662-57265-8_7

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.jacobi_reduction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (h : 0 < offDiagonalMass A) :
    ∃ Q : Matrix.unitaryGroup (Fin n) ℝ,
      offDiagonalMass (star (Q : Matrix (Fin n) (Fin n) ℝ) * A * (Q : Matrix (Fin n) (Fin n) ℝ)) < offDiagonalMass A := by sorry
