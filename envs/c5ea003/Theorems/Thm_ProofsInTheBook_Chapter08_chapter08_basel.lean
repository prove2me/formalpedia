-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter08_chapter08_basel
-- name    : ProofsInTheBook.Chapter08.chapter08_basel
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T14:42:59.171673+00:00
-- url     : https://prove2.me/theorems/e3996df6-ac4b-46de-ae6f-d6ff9a3e187c
-- title:
--   Chapter 8: the Basel sum
-- statement:
--   Define $a_0=0$ and $a_n=1/n^2$ for $n\ge1$. Then the sequence is summable and
--   $$\sum_{n=0}^{\infty}a_n=\sum_{n=1}^{\infty}\frac1{n^2}=\frac{\pi^2}{6}.$$
--   The explicit zero term matches the source's natural-number indexing. The source proof applies Mathlib's evaluation of this series.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 9, “Four times π²/6”, pp. 55–64 (https://doi.org/10.1007/978-3-662-57265-8_9). Exact Lean declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter08.lean#L32-L33. The book citation identifies the topic; the source proof’s reuse of Mathlib or local argument is described separately.

import Mathlib
open Real

theorem ProofsInTheBook.Chapter08.chapter08_basel : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) := by sorry
