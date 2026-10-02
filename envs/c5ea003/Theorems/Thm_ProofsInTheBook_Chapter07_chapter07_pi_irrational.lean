-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter07_chapter07_pi_irrational
-- name    : ProofsInTheBook.Chapter07.chapter07_pi_irrational
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T14:42:49.745985+00:00
-- url     : https://prove2.me/theorems/3943d66a-e68a-4453-8bc3-9ea4b511d7e1
-- title:
--   Chapter 7: irrationality of pi
-- statement:
--   The circle constant $\pi$ is irrational:
--   $$\pi\notin\mathbb Q.$$
--   This entry imports the source repository's direct application of Mathlib's irrationality theorem for $\pi$.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 8, “Some irrational numbers”, pp. 47–53 (https://doi.org/10.1007/978-3-662-57265-8_8). Exact Lean declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter07.lean#L220-L220. The book citation identifies the topic; the source proof’s reuse of Mathlib or local argument is described separately.

import Mathlib
set_option maxHeartbeats 800000
open scoped BigOperators

theorem ProofsInTheBook.Chapter07.chapter07_pi_irrational : Irrational Real.pi := by sorry
