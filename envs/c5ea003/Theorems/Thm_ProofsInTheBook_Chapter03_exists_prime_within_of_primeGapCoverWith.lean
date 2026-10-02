-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_prime_within_of_primeGapCoverWith
-- name    : ProofsInTheBook.Chapter03.exists_prime_within_of_primeGapCoverWith
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:26:32.343503+00:00
-- url     : https://prove2.me/theorems/e13bcaef-c8ab-4414-b821-3c45a86c9e02
-- title:
--   A bounded prime gap from a covering list
-- statement:
--   Let $g,L,r,m\in\mathbb N$ and let $s$ be a finite list of natural numbers. Assume $r\le m<L$ and `PrimeGapCoverWith g L r s`: a nonempty prefix $p_1,\ldots,p_t$ consists of primes, satisfies $p_i\le p_{i-1}+g$ with $p_0=r$, and ends with $L\le p_t$. Then
--   $$\exists p\text{ prime},\qquad m<p\le m+g.$$
--   The list is not required to be increasing, and no separate positivity assumption on $g$ is present.
--
--   This transfers the supplied list certificate to a local prime-existence bound.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L3508. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.exists_prime_within_of_primeGapCoverWith {gap limit prev m : ℕ} {ps : List ℕ}
    (hcover : PrimeGapCoverWith gap limit prev ps) (hprev : prev ≤ m) (hm : m < limit) :
    ∃ p, m < p ∧ p ≤ m + gap ∧ p.Prime := by sorry
