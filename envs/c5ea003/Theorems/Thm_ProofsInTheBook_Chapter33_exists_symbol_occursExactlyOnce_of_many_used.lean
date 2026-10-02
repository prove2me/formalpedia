-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_exists_symbol_occursExactlyOnce_of_many_used
-- name    : ProofsInTheBook.Chapter33.exists_symbol_occursExactlyOnce_of_many_used
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:06:01.444371+00:00
-- url     : https://prove2.me/theorems/034ca7f2-0079-4866-92af-1b8421c7468d
-- title:
--   A uniquely occurring symbol in a sparse array using many symbols
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. Let $n\in\mathbb N$ and $P$ have order $n$. If $|F(P)|\le\max(n-1,0)$ and $n<2|U(P)|$, then
--   $$\exists a\in[n],\quad|\{(i,j)\in[n]^2:P(i,j)=a\}|=1.$$
--    No partial Latin condition is required.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L816. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

theorem ProofsInTheBook.Chapter33.exists_symbol_occursExactlyOnce_of_many_used {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hcard : (filledCells P).card ≤ n - 1)
    (hmany : n < 2 * (usedSymbols P).card) :
    ∃ a : Fin n, SymbolOccursExactlyOnce P a := by sorry
