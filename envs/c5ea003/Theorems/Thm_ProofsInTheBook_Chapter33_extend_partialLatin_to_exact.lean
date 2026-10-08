-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_extend_partialLatin_to_exact
-- name    : ProofsInTheBook.Chapter33.extend_partialLatin_to_exact
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:06:18.372199+00:00
-- url     : https://prove2.me/theorems/efc44669-fe0f-4d97-aa24-07d88a988f57
-- title:
--   Padding a sparse partial Latin array to the exact Evans bound
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. Let $n\in\mathbb N$ and let $P$ be partial Latin with $|F(P)|\le\max(n-1,0)$. There exists a partial Latin array $Q$ of order $n$ such that
--   $$P(i,j)=a\in[n]\Rightarrow Q(i,j)=a,\qquad |F(Q)|=\max(n-1,0).$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33.lean#L1028. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

theorem ProofsInTheBook.Chapter33.extend_partialLatin_to_exact {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ Q : Fin n → Fin n → Option (Fin n),
      IsPartialLatin Q ∧ ExtendsPartial P Q ∧ (filledCells Q).card = n - 1 := by sorry
