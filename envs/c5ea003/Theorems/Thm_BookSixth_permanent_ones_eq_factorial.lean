-- Prove2me | Theorems.Thm_BookSixth_permanent_ones_eq_factorial
-- name    : BookSixth.permanent_ones_eq_factorial
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T07:56:59.23754+00:00
-- url     : https://prove2.me/theorems/5d1e50eb-907c-49fa-a3df-d11bf40f5fb7
-- title:
--   Chapter 37 adapter: permanent of the all-ones matrix
-- statement:
--   The permanent of the n-by-n all-ones matrix is n!. Check-case linking permanent counts to factorials for the Chapter 37 counting assembly.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, all-ones permanent identity used in the counting assembly, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_ones_eq_factorial (n : ℕ) :
    Matrix.permanent (fun (_ : Fin n) (_ : Fin n) => (1 : ℝ)) = (n.factorial : ℝ) := by sorry
