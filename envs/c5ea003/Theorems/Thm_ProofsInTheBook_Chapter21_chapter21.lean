-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter21_chapter21
-- name    : ProofsInTheBook.Chapter21.chapter21
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T15:17:55.074897+00:00
-- url     : https://prove2.me/theorems/47e2e051-093a-476f-a753-0b7fd7f5c152
-- title:
--   Integer-valued polynomials in the binomial basis
-- statement:
--   Let $P\in\mathbb Q[X]$ satisfy $P(z)\in\mathbb Z$ for every integer $z$. Define the forward-difference operator by $(\Delta f)(x)=f(x+1)-f(x)$, with $\Delta^0f=f$. There is a sequence $(c_k)_{k\ge0}$ of integers such that, for every $k\ge0$,
--   $$c_k=(\Delta^kP)(0),$$
--   and the following identity holds in $\mathbb Q[X]$:
--   $$P(X)=\sum_{k=0}^{d}c_k\binom{X}{k},\qquad \binom{X}{k}=\frac{X(X-1)\cdots(X-k+1)}{k!}.$$
--   Here $d$ is the degree of $P$ when $P\ne0$, and $d=0$ for the zero polynomial, and $\binom{X}{0}=1$. The coefficient identity is asserted for all natural $k$, not only $k\le d$.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 23, “A theorem of Pólya on polynomials”, pp. 163–168 (https://doi.org/10.1007/978-3-662-57265-8_23). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter21.lean#L231. The book citation identifies the topic; the selected declaration does not claim to reproduce the entire chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter21
open Finset Function Polynomial
open ProofsInTheBook.Chapter21

theorem ProofsInTheBook.Chapter21.chapter21 (P : ℚ[X]) (hP : IsIntegerValuedPolynomial P) :
    ∃ c : ℕ → ℤ,
      (∀ k : ℕ, (c k : ℚ) = ((fwdDiff (1 : ℚ))^[k] P.eval) 0) ∧
        P = ∑ k ∈ range (P.natDegree + 1), (c k : ℚ) • binomialPolynomial k := by sorry
