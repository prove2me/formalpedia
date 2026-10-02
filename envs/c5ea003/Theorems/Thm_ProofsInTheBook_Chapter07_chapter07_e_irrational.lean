-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter07_chapter07_e_irrational
-- name    : ProofsInTheBook.Chapter07.chapter07_e_irrational
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T14:42:50.255212+00:00
-- url     : https://prove2.me/theorems/3ff3ad5f-cb7c-42e5-9277-317ece6b0a43
-- title:
--   Chapter 7: irrationality of e
-- statement:
--   The number $e=\exp(1)$ is irrational:
--   $$e\notin\mathbb Q.$$
--   The source formalization uses the factorial-series argument, bounding a scaled tail strictly between zero and one.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 8, “Some irrational numbers”, pp. 47–53 (https://doi.org/10.1007/978-3-662-57265-8_8). Exact Lean declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter07.lean#L171-L208. The book citation identifies the topic; the source proof’s reuse of Mathlib or local argument is described separately.

import Mathlib
set_option maxHeartbeats 800000
open scoped BigOperators

theorem ProofsInTheBook.Chapter07.chapter07_e_irrational : Irrational (Real.exp 1) := by sorry
