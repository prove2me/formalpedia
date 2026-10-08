-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter04_ZagierTriple_exists_sq_add_sq_of_prime_mod_four_eq_one
-- name    : ProofsInTheBook.Chapter04.ZagierTriple.exists_sq_add_sq_of_prime_mod_four_eq_one
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T14:40:35.37607+00:00
-- url     : https://prove2.me/theorems/d6c95d70-0266-46ea-b066-11feb9ab2fd7
-- title:
--   Chapter 4: a prime congruent to 1 modulo 4 is a sum of two squares
-- statement:
--   Let $p$ be a prime natural number satisfying $p\equiv1\pmod4$. Then there exist natural numbers $a,b$ such that
--   $$a^2+b^2=p.$$
--   This formalization follows Zagier's finite-involution argument. It proves the sufficiency direction for primes; it does not assert the full characterization of all integers representable as a sum of two squares.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, sixth edition (2018), Chapter 4, Representing numbers as sums of two squares; https://doi.org/10.1007/978-3-662-57265-8. Exact Lean source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter04.lean#L552-L564

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter04
open Nat
open ProofsInTheBook.Chapter04
open ProofsInTheBook.Chapter04.ZagierTriple

theorem ProofsInTheBook.Chapter04.ZagierTriple.exists_sq_add_sq_of_prime_mod_four_eq_one (p : ℕ) (hp : p.Prime)
    (hmod : p % 4 = 1) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by sorry
