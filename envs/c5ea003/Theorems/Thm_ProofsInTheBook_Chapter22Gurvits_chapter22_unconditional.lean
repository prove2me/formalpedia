-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter22Gurvits_chapter22_unconditional
-- name    : ProofsInTheBook.Chapter22Gurvits.chapter22_unconditional
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:05:06.412574+00:00
-- url     : https://prove2.me/theorems/14ff3de4-8156-4b54-9152-a35ea99f6cbf
-- title:
--   Van der Waerden’s permanent lower bound
-- statement:
--   For every natural number $n$ and every real $n\times n$ doubly stochastic matrix $A$ (all entries nonnegative and all row and column sums equal to 1), $$\operatorname{per}(A)\geq\frac{n!}{n^n}.$$ At $n=0$ the empty permanent and the right-hand side both equal 1, using $0^0=1$. No capacity, stability, factorization, or positivity certificate is an additional hypothesis.
-- source:
--   Repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Gurvits.lean#L1732. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture”, pp. 169–177 (https://doi.org/10.1007/978-3-662-57265-8_24). Auxiliary statements are cited to the repository and are not asserted to be separately numbered book theorems.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22
set_option autoImplicit true
open ProofsInTheBook.Chapter22Gurvits
open scoped BigOperators
open ProofsInTheBook.Chapter22

theorem ProofsInTheBook.Chapter22Gurvits.chapter22_unconditional (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by sorry
