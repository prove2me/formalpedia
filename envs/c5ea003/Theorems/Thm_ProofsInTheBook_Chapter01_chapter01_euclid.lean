-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter01_chapter01_euclid
-- name    : ProofsInTheBook.Chapter01.chapter01_euclid
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T13:33:48.236869+00:00
-- url     : https://prove2.me/theorems/eff43ab9-5299-468c-a882-84f6acabcecf
-- title:
--   Chapter 1 — Infinitely many primes (Euclid)
-- statement:
--   Let $\mathcal P=\{p\in\mathbb N:p\text{ is prime}\}$. Then
--
--   $$\mathcal P\text{ is infinite}.$$
--
--   There is no finite list containing every prime number. The statement has no additional hypotheses. This entry preserves the finite-product proof in the source repository's first chapter.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, sixth edition, 2018, Chapter “Six proofs of the infinity of primes”, pp. 3–8; https://doi.org/10.1007/978-3-662-57265-8. Exact Lean declaration and proof: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter01.lean#L6-L39

import Mathlib
import Mathlib.NumberTheory.LucasLehmer

theorem ProofsInTheBook.Chapter01.chapter01_euclid : Infinite {p : ℕ // p.Prime} := by sorry
