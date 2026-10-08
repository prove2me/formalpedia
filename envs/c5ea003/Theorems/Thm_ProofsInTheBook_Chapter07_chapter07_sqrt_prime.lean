-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter07_chapter07_sqrt_prime
-- name    : ProofsInTheBook.Chapter07.chapter07_sqrt_prime
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T14:42:52.765908+00:00
-- url     : https://prove2.me/theorems/42444c3c-4790-4212-8467-718831357ed3
-- title:
--   Chapter 7: the square root of a prime is irrational
-- statement:
--   For every prime natural number $p$, the nonnegative real square root of $p$ is irrational:
--   $$\sqrt p\notin\mathbb Q.$$
--   The source uses the characterization of irrational square roots of natural numbers together with the fact that a prime is not a square.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 8, “Some irrational numbers”, pp. 47–53 (https://doi.org/10.1007/978-3-662-57265-8_8). Exact Lean declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter07.lean#L37-L39. The book citation identifies the topic; the source proof’s reuse of Mathlib or local argument is described separately.

import Mathlib
set_option maxHeartbeats 800000
open scoped BigOperators

theorem ProofsInTheBook.Chapter07.chapter07_sqrt_prime (p : ℕ) (hp : p.Prime) : Irrational (√(p : ℝ)) := by sorry
