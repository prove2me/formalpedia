-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_chapter33_unconditional
-- name    : ProofsInTheBook.Chapter33.chapter33_unconditional
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:05:51.421119+00:00
-- url     : https://prove2.me/theorems/39bf0931-0874-4c06-acdf-197a469b32b0
-- title:
--   Evans–Smetaniuk completion theorem
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. For every $n\in\mathbb N$ and every partial Latin array $P$ of order $n$,
--   $$|F(P)|\le\max(n-1,0)\quad\Longrightarrow\quad P\text{ has a completion of order }n.$$
--    Natural-number subtraction includes the empty order-zero array.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Unconditional.lean#L39. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open ProofsInTheBook.Chapter33

theorem ProofsInTheBook.Chapter33.chapter33_unconditional :
    ∀ n : ℕ, LatinSquareCompletionTheorem n := by sorry
