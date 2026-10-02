-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_SmetBackDiagonalCompletableCore
-- name    : ProofsInTheBook.Chapter33.SmetBackDiagonalCompletableCore
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:05:42.276371+00:00
-- url     : https://prove2.me/theorems/bc16b731-c1b5-4164-a888-020e63309a75
-- title:
--   Completion of the Smetaniuk back-diagonal partial array
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. Let $N\ge3$ be a natural number and let $L_0:[N]^2\to[N]$ be Latin, meaning injective in every row and column. For $L_0:[N]^2\to[N]$, define $B_{L_0}:[N+1]^2\to[N+1]\cup\{\bot\}$ by
--   $$B_{L_0}(i,j)=\begin{cases}L_0(i,j)&i+j<N,\\N&i+j=N,\\\bot&i+j>N.\end{cases}$$
--    There exists a Latin square $L:[N+1]^2\to[N+1]$ completing $B_{L_0}$. Equivalently,
--   $$L(i,j)=L_0(i,j)\ (i+j<N),\qquad L(i,j)=N\ (i+j=N).$$
--    The quantified cells lie in $[N+1]^2$.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L2802. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

theorem ProofsInTheBook.Chapter33.SmetBackDiagonalCompletableCore {N : ℕ} (hN : 3 ≤ N)
    (L₀ : Fin N → Fin N → Fin N) (hL₀ : IsLatinSquare L₀) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetBackPartial L₀) L := by sorry
