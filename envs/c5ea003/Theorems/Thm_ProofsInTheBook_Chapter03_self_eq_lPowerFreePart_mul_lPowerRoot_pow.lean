-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_self_eq_lPowerFreePart_mul_lPowerRoot_pow
-- name    : ProofsInTheBook.Chapter03.self_eq_lPowerFreePart_mul_lPowerRoot_pow
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:37:04.716216+00:00
-- url     : https://prove2.me/theorems/13b2b6b1-29ff-4163-9361-ae672a77a4ae
-- title:
--   Decomposition into an l-power-free part and an lth power
-- statement:
--   Let $l,m\in\mathbb N$ with $m\ne0$. For each prime $p\mid m$, let $v_p(m)$ denote its exponent in $m$, and define
--   $$A_l(m)=\prod_{p\mid m}p^{v_p(m)\bmod l},\qquad B_l(m)=\prod_{p\mid m}p^{\lfloor v_p(m)/l\rfloor}.$$
--   Then
--   $$m=A_l(m)B_l(m)^l.$$
--   The products run over prime divisors. The statement also includes $l=0$, with Lean’s natural-number conventions $e\bmod0=e$ and $e/0=0$, so $A_0(m)=m$ and $B_0(m)=1$.
--
--   This is the exact arithmetic decomposition used by the divisibility arguments.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L4159. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03
open scoped BigOperators

lemma ProofsInTheBook.Chapter03.self_eq_lPowerFreePart_mul_lPowerRoot_pow (l m : ℕ) (hm : m ≠ 0) :
    m = lPowerFreePart l m * (lPowerRoot l m) ^ l := by sorry
