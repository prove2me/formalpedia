-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_pow_l_dvd_one_factor_of_descFactorial
-- name    : ProofsInTheBook.Chapter03.pow_l_dvd_one_factor_of_descFactorial
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:27:20.964776+00:00
-- url     : https://prove2.me/theorems/3c8279ba-8bfb-4a6a-ab3e-297f9ea182ae
-- title:
--   A large prime power dividing a short falling factorial divides one factor
-- statement:
--   Let $n,k,l,p\in\mathbb N$. Assume $p$ is prime, $k<p$, $0<l$, $k\le n$, and
--   $$p^l\mid n^{\underline{k}},\qquad n^{\underline{k}}=\prod_{j=0}^{k-1}(n-j).$$
--   Then
--   $$\exists i\in\mathbb N,\qquad i<k\quad\text{and}\quad p^l\mid n-i.$$
--
--   This concentrates the divisibility by a prime power in one of the consecutive factors.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L4036. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

lemma ProofsInTheBook.Chapter03.pow_l_dvd_one_factor_of_descFactorial {n k l p : ℕ} (hp : p.Prime) (hkp : k < p)
    (hlp : 0 < l) (hk_le_n : k ≤ n) (hp_l_dvd : p ^ l ∣ n.descFactorial k) :
    ∃ i, i < k ∧ p ^ l ∣ n - i := by sorry
