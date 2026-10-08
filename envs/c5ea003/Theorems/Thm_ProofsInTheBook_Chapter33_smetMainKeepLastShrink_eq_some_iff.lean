-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_smetMainKeepLastShrink_eq_some_iff
-- name    : ProofsInTheBook.Chapter33.smetMainKeepLastShrink_eq_some_iff
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:07:02.96402+00:00
-- url     : https://prove2.me/theorems/ebf8e293-69a8-48ba-a8b6-e2d54993b417
-- title:
--   Cell correspondence for the last-column-preserving shrink
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. Let $N\in\mathbb N$ and let $P:[N+1]^2\to[N+1]\cup\{\bot\}$ be any partial array. For $P:[N+1]^2\to[N+1]\cup\{\bot\}$, define $Q:[N]^2\to[N]\cup\{\bot\}$ by retaining $P(i,N-j)$ if its value is smaller than $N$, and setting $Q(i,j)=\bot$ otherwise. For all $i,j,a\in[N]$,
--   $$Q(i,j)=a\quad\Longleftrightarrow\quad P(i,N-j)=a.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L2115. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

lemma ProofsInTheBook.Chapter33.smetMainKeepLastShrink_eq_some_iff {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)))
    (i j : Fin N) (a : Fin N) :
    smetMainKeepLastShrink P i j = some a ↔
      P (Fin.castSucc i) (Fin.rev (Fin.castSucc j)) = some (Fin.castSucc a) := by sorry
