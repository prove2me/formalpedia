-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_exists_interval_prime_of_34_le_lt_36
-- name    : ProofsInTheBook.Chapter03.exists_interval_prime_of_34_le_lt_36
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:35:55.139631+00:00
-- url     : https://prove2.me/theorems/8afaa5e0-e505-420b-81bf-c67140c1cd05
-- title:
--   An interval prime for k equal to 34 or 35
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $34\le k<36$, $2k\le n$, and $n<k^2$. There is a prime p such that
--   $$k<p,\qquad n-k<p\le n.$$
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L3728. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.exists_interval_prime_of_34_le_lt_36
    {n k : ℕ} (hk34 : 34 ≤ k) (hk36 : k < 36) (hn2k : 2 * k ≤ n)
    (hnsq : n < k * k) :
    ∃ p, k < p ∧ n - k < p ∧ p ≤ n ∧ p.Prime := by sorry
