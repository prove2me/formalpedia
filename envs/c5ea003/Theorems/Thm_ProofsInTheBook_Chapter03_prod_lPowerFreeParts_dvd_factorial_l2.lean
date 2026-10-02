-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_prod_lPowerFreeParts_dvd_factorial_l2
-- name    : ProofsInTheBook.Chapter03.prod_lPowerFreeParts_dvd_factorial_l2
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:26.588214+00:00
-- url     : https://prove2.me/theorems/aec41160-6821-45d0-ad94-051910294e43
-- title:
--   Square-free parts divide k! when a binomial coefficient is a square
-- statement:
--   Let $n,k,m\in\mathbb N$ satisfy $4\le k$, $2k\le n$, and $\binom nk=m^2$. For positive $u$, define $A_2(u)=\prod_{p\mid u}p^{v_p(u)\bmod2}$ over prime divisors, where $v_p(u)$ is the prime exponent. Then
--   $$\prod_{j=0}^{k-1}A_2(n-j)\mid k!.$$
--
--   This is the square-case divisibility lemma, retaining the hypothetical square equality.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L5251. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.prod_lPowerFreeParts_dvd_factorial_l2
    {n k m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (h_eq : n.choose k = m ^ 2) :
    (∏ j ∈ Finset.range k, lPowerFreePart 2 (n - j)) ∣ k ! := by sorry
