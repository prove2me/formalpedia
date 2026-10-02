-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_isPartialLatin_relabelPartial
-- name    : ProofsInTheBook.Chapter33.isPartialLatin_relabelPartial
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:06:17.667521+00:00
-- url     : https://prove2.me/theorems/f254d806-8893-4fb7-bcd6-db22bfce17b2
-- title:
--   Partial Latin arrays are preserved by independent relabeling
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. For permutations $\rho,\kappa,\sigma$ of $[n]$, put $P^{\rho,\kappa,\sigma}(i,j)=\sigma(P(\rho(i),\kappa(j)))$, where $\sigma(\bot)=\bot$; row and column permutations map new coordinates to old coordinates. For every $n\in\mathbb N$, partial Latin $P$ of order $n$, and triple of permutations $\rho,\kappa,\sigma$,
--   $$P^{\rho,\kappa,\sigma}\text{ is partial Latin}.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33.lean#L449. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

lemma ProofsInTheBook.Chapter33.isPartialLatin_relabelPartial {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P) :
    IsPartialLatin (relabelPartial rowPerm colPerm symPerm P) := by sorry
