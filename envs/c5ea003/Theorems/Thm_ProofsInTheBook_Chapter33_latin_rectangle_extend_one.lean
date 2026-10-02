-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_latin_rectangle_extend_one
-- name    : ProofsInTheBook.Chapter33.latin_rectangle_extend_one
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:06:25.411494+00:00
-- url     : https://prove2.me/theorems/41b12d4d-3ea4-4f69-9fc2-28f10e6121ce
-- title:
--   Adjoining one row to a Latin rectangle
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. Let $r,n\in\mathbb N$ satisfy $r<n$, and let $R:[r]\times[n]\to[n]$ be injective in each row and column. There exists an injective map $f:[n]\to[n]$ such that
--   $$\forall i\in[r],\ \forall j\in[n],\quad f(j)\ne R(i,j).$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33.lean#L245. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

theorem ProofsInTheBook.Chapter33.latin_rectangle_extend_one {r n : ℕ} (R : Fin r → Fin n → Fin n)
    (hrow : ∀ i : Fin r, Function.Injective (R i))
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j)
    (hrn : r < n) :
    ∃ row : Fin n → Fin n, Function.Injective row ∧ ∀ i j, row j ≠ R i j := by sorry
