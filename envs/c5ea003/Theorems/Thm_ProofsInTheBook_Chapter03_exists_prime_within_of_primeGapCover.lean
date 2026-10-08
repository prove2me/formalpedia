-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_prime_within_of_primeGapCover
-- name    : ProofsInTheBook.Chapter03.exists_prime_within_of_primeGapCover
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:45.146614+00:00
-- url     : https://prove2.me/theorems/c619b9aa-772a-48fa-9b60-cfc9e0ee333c
-- title:
--   A prime within 36 from a prime-gap cover
-- statement:
--   Let $L,r,m\in\mathbb N$, and let $s$ be a finite list of natural numbers. Assume $r\le m<L$ and `PrimeGapCover L r s`. Explicitly, $s$ has a nonempty prefix $p_1,\ldots,p_t$ consisting of primes, with $p_0=r$, $p_i\le p_{i-1}+36$ for $1\le i\le t$, and $L\le p_t$. Then
--   $$\exists p\text{ prime},\qquad m<p\le m+36.$$
--   No monotonicity of the covering list is assumed.
--
--   This is a certificate-consumption lemma; a valid prime-gap cover remains an explicit input.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L3823. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.exists_prime_within_of_primeGapCover {limit prev m : ℕ} {ps : List ℕ}
    (hcover : PrimeGapCover limit prev ps) (hprev : prev ≤ m) (hm : m < limit) :
    ∃ p, m < p ∧ p ≤ m + 36 ∧ p.Prime := by sorry
