-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_interval_prime_below_sq_k_lt_120_sqrt33_cert
-- name    : ProofsInTheBook.Chapter03.interval_prime_below_sq_k_lt_120_sqrt33_cert
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:26:57.478546+00:00
-- url     : https://prove2.me/theorems/b6e2210b-2058-40bd-8b8e-9a7d0dedf093
-- title:
--   A certified interval prime for k below 120
-- statement:
--   Let $k,n\in\mathbb N$ satisfy $k<120$, $n<14400$, $9\le k$, $33\le\lfloor\sqrt n\rfloor$, $2k\le n$, and $n<k^2$. Let $p=\operatorname{nextPrimeWithin}(36,n-k)$, obtained by scanning the next 36 consecutive integers and returning the first prime if one is found. Then
--   $$k<p,\qquad n-k<p\le n,\qquad p\text{ is prime}.$$
--   The square root in the hypotheses is the integer square root.
--
--   This is a finite-range interval-prime certificate used in the binomial-factor argument.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L3846. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.interval_prime_below_sq_k_lt_120_sqrt33_cert :
    ∀ k : Fin 120, ∀ n : Fin 14400,
      9 ≤ k.val → 33 ≤ sqrt n.val → 2 * k.val ≤ n.val → n.val < k.val * k.val →
        let p := nextPrimeWithin 36 (n.val - k.val)
        k.val < p ∧ n.val - k.val < p ∧ p ≤ n.val ∧ Nat.Prime p := by sorry
