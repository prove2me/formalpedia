-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter32_chapter32
-- name    : ProofsInTheBook.Chapter32.chapter32
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:10:58.545588+00:00
-- url     : https://prove2.me/theorems/9f9f3a48-7ca5-4852-997b-0a38e43fecca
-- title:
--   Three binomial coefficient identities
-- statement:
--   For all natural numbers $m,n,k$, the following binomial identities hold:
--   $$ {m+n\choose k}=\sum_{\substack{i,j\in\mathbb N\\i+j=k}}{m\choose i}{n\choose j},\qquad \sum_{i=k}^{n}{i\choose k}={n+1\choose k+1},\qquad \sum_{i=0}^{n}{n\choose i}=2^n.$$
--   A binomial coefficient is zero when its lower argument exceeds its upper argument; the middle sum is empty when $n<k$.
--
--   This declaration packages Vandermonde’s convolution, the hockey-stick identity, and the sum of a binomial row.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 34, “Identities versus bijections”, pp. 241–246 (https://doi.org/10.1007/978-3-662-57265-8_34). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter32.lean#L75. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
open Nat Finset Polynomial

theorem ProofsInTheBook.Chapter32.chapter32 :
    (∀ m n k : ℕ,
        (m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2) ∧
      (∀ n k : ℕ, ∑ i ∈ Icc k n, i.choose k = (n + 1).choose (k + 1)) ∧
      (∀ n : ℕ, ∑ k ∈ range (n + 1), n.choose k = 2 ^ n) := by sorry
