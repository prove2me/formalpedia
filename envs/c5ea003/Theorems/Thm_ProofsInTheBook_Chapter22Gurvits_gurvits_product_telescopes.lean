-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter22Gurvits_gurvits_product_telescopes
-- name    : ProofsInTheBook.Chapter22Gurvits.gurvits_product_telescopes
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:05:59.928358+00:00
-- url     : https://prove2.me/theorems/52717d8b-d5a4-4be2-bf56-5c7f68085838
-- title:
--   The Gurvits factors telescope to the factorial ratio
-- statement:
--   For every integer $n\geq1$, put $G(k)=((k-1)/k)^{k-1}$ for $k\geq2$. Then $$\prod_{k=2}^{n}G(k)=\frac{n!}{n^n}.$$ For $n=1$ the product is empty and equals 1.
-- source:
--   Repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Gurvits.lean#L35. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture”, pp. 169–177 (https://doi.org/10.1007/978-3-662-57265-8_24). Auxiliary statements are cited to the repository and are not asserted to be separately numbered book theorems.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22
set_option autoImplicit true
open ProofsInTheBook.Chapter22Gurvits
open scoped BigOperators
open ProofsInTheBook.Chapter22

theorem ProofsInTheBook.Chapter22Gurvits.gurvits_product_telescopes (n : ℕ) (hn : 1 ≤ n) :
    ∏ m ∈ Finset.Icc 2 n, G m = (n.factorial : ℝ) / (n : ℝ) ^ n := by sorry
