-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_rowSymbolConjugate_eq_some_iff
-- name    : ProofsInTheBook.Chapter33.rowSymbolConjugate_eq_some_iff
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:06:32.911183+00:00
-- url     : https://prove2.me/theorems/7af97d15-b66a-4a19-a244-5bef9fab8d30
-- title:
--   The cell relation under row-symbol conjugation
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. For partial Latin $P$, its row-symbol conjugate $P^*$ satisfies $P^*(a,j)=i$ if $P(i,j)=a$, and is empty when no such row exists; column uniqueness makes the row unique. For every $n\in\mathbb N$, partial Latin $P$ of order $n$, and $a,j,i\in[n]$,
--   $$P^*(a,j)=i\quad\Longleftrightarrow\quad P(i,j)=a.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Ryser.lean#L208. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

lemma ProofsInTheBook.Chapter33.rowSymbolConjugate_eq_some_iff {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P)
    (e c r : Fin n) :
    rowSymbolConjugate P e c = some r ↔ P r c = some e := by sorry
