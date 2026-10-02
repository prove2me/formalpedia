-- Prove2me | Theorems.Thm_BookSixth_spectral
-- name    : BookSixth.spectral
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-13T01:35:56.737289+00:00
-- url     : https://prove2.me/theorems/d8387b3c-83c8-4d3a-b863-b32c5a1bbf3e
-- title:
--   Chapter 7, Theorem 1: spectral theorem
-- statement:
--   Every real symmetric square matrix can be diagonalized by a real orthogonal change of basis. The dimension may be zero; the real unitary group is the orthogonal group.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 7, Theorem 1: spectral theorem, p. 39. https://doi.org/10.1007/978-3-662-57265-8_7

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.spectral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∃ Q : Matrix.unitaryGroup (Fin n) ℝ, ∃ d : Fin n → ℝ,
      star (Q : Matrix (Fin n) (Fin n) ℝ) * A * (Q : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal d := by sorry
