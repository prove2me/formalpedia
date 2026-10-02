-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_filledCells_relabelPartial
-- name    : ProofsInTheBook.Chapter33.filledCells_relabelPartial
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:06:10.22495+00:00
-- url     : https://prove2.me/theorems/030a0cfd-c701-45ef-ab21-7e4a9a91756c
-- title:
--   Filled cells under independent relabeling
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. For permutations $\rho,\kappa,\sigma$ of $[n]$, put $P^{\rho,\kappa,\sigma}(i,j)=\sigma(P(\rho(i),\kappa(j)))$, where $\sigma(\bot)=\bot$; row and column permutations map new coordinates to old coordinates. For every $n\in\mathbb N$, partial array $P$ of order $n$, and triple of permutations,
--   $$F(P^{\rho,\kappa,\sigma})=\{(\rho^{-1}(i),\kappa^{-1}(j)):(i,j)\in F(P)\}.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33.lean#L529. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

lemma ProofsInTheBook.Chapter33.filledCells_relabelPartial {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) :
    filledCells (relabelPartial rowPerm colPerm symPerm P) =
      (filledCells P).image (fun ij : Fin n × Fin n =>
        (rowPerm.symm ij.1, colPerm.symm ij.2)) := by sorry
