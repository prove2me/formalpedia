-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter05_chapter05_quadratic_reciprocity
-- name    : ProofsInTheBook.Chapter05.chapter05_quadratic_reciprocity
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T14:42:40.524458+00:00
-- url     : https://prove2.me/theorems/cd151382-ff47-4d0b-b1e6-23c97aed030c
-- title:
--   Chapter 5: quadratic reciprocity
-- statement:
--   Let $p$ and $q$ be distinct odd primes. Writing $(a/\ell)$ for the Legendre symbol modulo an odd prime $\ell$, we have
--   $$\left(\frac{p}{q}\right)\left(\frac{q}{p}\right)=(-1)^{\frac{p-1}{2}\frac{q-1}{2}}.$$
--   The primality, oddness, and distinctness assumptions are all retained. The source proof invokes Mathlib's quadratic reciprocity theorem.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, sixth edition (2018), Chapter 5; https://doi.org/10.1007/978-3-662-57265-8. Exact Lean declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter05.lean#L27-L30

import Mathlib

theorem ProofsInTheBook.Chapter05.chapter05_quadratic_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by sorry
