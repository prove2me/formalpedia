-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter06_chapter06_wedderburn
-- name    : ProofsInTheBook.Chapter06.chapter06_wedderburn
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T14:42:46.166687+00:00
-- url     : https://prove2.me/theorems/28ed9c2d-4461-4d69-b0ec-b3aaae5cf350
-- title:
--   Chapter 6: every finite division ring is commutative
-- statement:
--   Let $D$ be a finite division ring. Then multiplication in $D$ is commutative:
--   $$ab=ba\qquad\text{for all }a,b\in D.$$
--   Thus every finite division ring is a field. The source uses Mathlib's commutative-ring instance for finite division rings.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, sixth edition (2018), Chapter 6; https://doi.org/10.1007/978-3-662-57265-8. Exact Lean declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter06.lean#L24-L26

import Mathlib

theorem ProofsInTheBook.Chapter06.chapter06_wedderburn (D : Type*) [DivisionRing D] [Finite D]
    (a b : D) : a * b = b * a := by sorry
