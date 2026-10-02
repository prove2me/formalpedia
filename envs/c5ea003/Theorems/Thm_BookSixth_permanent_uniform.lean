-- Prove2me | Theorems.Thm_BookSixth_permanent_uniform
-- name    : BookSixth.permanent_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:25:01.956377+00:00
-- url     : https://prove2.me/theorems/f24a36e2-57ac-4ac5-b310-96198201490b
-- title:
--   Chapter 37 adapter: permanent of the uniform matrix
-- statement:
--   For positive $n$, the permanent of the $n \times n$ uniform matrix with all entries $1/n$ equals $n!/n^n$: the equality case of van der Waerden's bound behind Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, van der Waerden equality case adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_uniform (n : ℕ) (hn : 0 < n) :
    Matrix.permanent (fun (_ : Fin n) (_ : Fin n) => ((n : ℝ))⁻¹) = (n.factorial : ℝ) / (n : ℝ) ^ n := by sorry
