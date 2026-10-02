-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_three_mul_primeCounting_le_30_150_cert
-- name    : ProofsInTheBook.Chapter03.three_mul_primeCounting_le_30_150_cert
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:35.803517+00:00
-- url     : https://prove2.me/theorems/d2259190-ba82-4de7-8528-562283ea0625
-- title:
--   At most k/3 primes up to k in the range 33 to 149
-- statement:
--   Let $k\in\mathbb N$ satisfy $33\le k<150$. Write $\pi(t)=|\{p\in\mathbb N:p\le t\text{ and }p\text{ is prime}\}|$. Then
--   $$3\pi(k)\le k.$$
--
--   This finite-range certificate supplies the base range of the general prime-counting bound.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L804. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.three_mul_primeCounting_le_30_150_cert :
    ∀ k : Fin 150, 33 ≤ k.val → 3 * Nat.primeCounting k.val ≤ k.val := by sorry
