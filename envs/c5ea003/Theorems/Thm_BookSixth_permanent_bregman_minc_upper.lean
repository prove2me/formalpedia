-- Prove2me | Theorems.Thm_BookSixth_permanent_bregman_minc_upper
-- name    : BookSixth.permanent_bregman_minc_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:27:46.929287+00:00
-- url     : https://prove2.me/theorems/b35f2b19-4a72-4ba9-abdd-33a1fbdeea7c
-- title:
--   Chapter 37 lemma: Bregman-Minc permanent upper bound
-- statement:
--   Bregman's theorem (Minc conjecture): the permanent of a $0$-$1$ matrix with row sums $r_i$ is at most $\prod_i (r_i!)^{1/r_i}$. This is the permanent estimate behind the upper counting bound of Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, permanent upper bound used for Theorem 2, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.permanent_bregman_minc_upper (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℕ) (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) (hrow : ∀ i, ∑ j, M i j = (r i : ℝ)) :
    Matrix.permanent M ≤ ∏ i, ((r i).factorial : ℝ) ^ ((1 : ℝ) / (r i : ℝ)) := by sorry
