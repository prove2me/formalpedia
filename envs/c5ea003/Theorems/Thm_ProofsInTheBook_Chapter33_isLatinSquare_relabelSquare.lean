-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_isLatinSquare_relabelSquare
-- name    : ProofsInTheBook.Chapter33.isLatinSquare_relabelSquare
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:06:21.570591+00:00
-- url     : https://prove2.me/theorems/00f9395d-633e-4496-ba25-eee915dc29ff
-- title:
--   Latin squares are preserved by independent relabeling
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. Let $n\in\mathbb N$, let $L:[n]^2\to[n]$ be injective in each row and column, and let $\rho,\kappa,\sigma$ be permutations of $[n]$. Then
--   $$L^{\prime}(i,j)=\sigma(L(\rho(i),\kappa(j)))$$
--    is injective in each row and column, hence Latin.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33.lean#L471. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

lemma ProofsInTheBook.Chapter33.isLatinSquare_relabelSquare {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) :
    IsLatinSquare (relabelSquare rowPerm colPerm symPerm L) := by sorry
