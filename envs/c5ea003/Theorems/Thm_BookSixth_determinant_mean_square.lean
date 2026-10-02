-- Prove2me | Theorems.Thm_BookSixth_determinant_mean_square
-- name    : BookSixth.determinant_mean_square
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-13T01:37:32.850653+00:00
-- url     : https://prove2.me/theorems/bc06ffbb-4912-44a3-bb56-f16a732a49cb
-- title:
--   Chapter 7, Mean-square determinant identity
-- statement:
--   Summing the squared determinants over all sign matrices of order n gives 2^(n²) n!, equivalently the uniform mean square is n!. Order zero is included.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 7, Mean-square determinant identity, p. 45. https://doi.org/10.1007/978-3-662-57265-8_7

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.determinant_mean_square (n : ℕ) :
    (∑ B : Fin n → Fin n → Bool, (Matrix.det (fun i j => if B i j then (1 : ℝ) else -1))^2) = (2 : ℝ)^(n*n) * (n.factorial : ℝ) := by sorry
