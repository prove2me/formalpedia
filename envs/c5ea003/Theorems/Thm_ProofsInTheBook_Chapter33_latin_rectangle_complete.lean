-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_latin_rectangle_complete
-- name    : ProofsInTheBook.Chapter33.latin_rectangle_complete
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:06:30.505755+00:00
-- url     : https://prove2.me/theorems/a5c39977-300c-40d5-9d99-1fba807631ac
-- title:
--   Completing a Latin rectangle to a Latin square
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. Let $r,n\in\mathbb N$ satisfy $r\le n$, and let $R:[r]\times[n]\to[n]$ be injective in each row and each column. There exists a Latin square $L:[n]^2\to[n]$ with
--   $$\forall i\in[r],\ \forall j\in[n],\quad L(i,j)=R(i,j).$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Ryser.lean#L385. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

theorem ProofsInTheBook.Chapter33.latin_rectangle_complete {r n : ℕ} (R : Fin r → Fin n → Fin n)
    (hrow : ∀ i : Fin r, Function.Injective (R i))
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j)
    (hrn : r ≤ n) :
    ∃ L : Fin n → Fin n → Fin n,
      IsLatinSquare L ∧ ∀ i : Fin r, ∀ j,
        L (Fin.castLE hrn i) j = R i j := by sorry
