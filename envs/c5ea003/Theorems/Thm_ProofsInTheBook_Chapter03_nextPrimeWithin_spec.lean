-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_nextPrimeWithin_spec
-- name    : ProofsInTheBook.Chapter03.nextPrimeWithin_spec
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:27:11.028567+00:00
-- url     : https://prove2.me/theorems/1a30cb12-508d-43ba-b550-a4b36b130308
-- title:
--   Correctness of bounded consecutive prime search
-- statement:
--   Let $f,m,p\in\mathbb N$ with $p$ prime and $m<p\le m+f$. Define the bounded search $Q(0,u)=u$ and
--   $$Q(f+1,u)=\begin{cases}u+1,&u+1\text{ prime},\\Q(f,u+1),&\text{otherwise}.\end{cases}$$
--   Put $q=Q(f,m)$. Then
--   $$m<q\le p,\qquad q\text{ is prime}.$$
--   The function $Q$ is the encoded `nextPrimeWithin`.
--
--   A prime within the search budget is required; the lemma makes no unconditional prime-gap assertion.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L3794. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.nextPrimeWithin_spec {fuel m p : ℕ} (hp : p.Prime) (hmp : m < p)
    (hpfuel : p ≤ m + fuel) :
    let q := nextPrimeWithin fuel m
    m < q ∧ q ≤ p ∧ q.Prime := by sorry
