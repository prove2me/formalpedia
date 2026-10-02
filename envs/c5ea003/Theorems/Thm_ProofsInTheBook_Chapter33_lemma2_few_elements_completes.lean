-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_lemma2_few_elements_completes
-- name    : ProofsInTheBook.Chapter33.lemma2_few_elements_completes
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:06:40.255232+00:00
-- url     : https://prove2.me/theorems/0d5375be-254e-432f-9fe8-6d74f5abcc14
-- title:
--   Completion of a sparse partial Latin array with few symbols
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. Let $n\in\mathbb N$ and let $P$ be partial Latin of order $n$. If
--   $$|F(P)|+1\le n,\qquad 2|U(P)|\le n,$$
--    then $P$ has a completion of order $n$.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Ryser.lean#L1476. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

theorem ProofsInTheBook.Chapter33.lemma2_few_elements_completes (n : ℕ)
    (P : Fin n → Fin n → Option (Fin n)) (hP : IsPartialLatin P)
    (hcard : (filledCells P).card + 1 <= n)
    (helem : 2 * (elementsUsed P).card <= n) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by sorry
