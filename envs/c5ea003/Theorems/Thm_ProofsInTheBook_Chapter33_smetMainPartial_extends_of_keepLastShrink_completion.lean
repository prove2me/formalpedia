-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_smetMainPartial_extends_of_keepLastShrink_completion
-- name    : ProofsInTheBook.Chapter33.smetMainPartial_extends_of_keepLastShrink_completion
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:07:12.173738+00:00
-- url     : https://prove2.me/theorems/592e8ff9-5aa5-4f7f-84ea-0010b62f70fa
-- title:
--   Extending a normalized array from a completed shrink
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. Let $N\in\mathbb N$, $P:[N+1]^2\to[N+1]\cup\{\bot\}$, $L_0:[N]^2\to[N]$, and $d\in[N+1]$. For $P:[N+1]^2\to[N+1]\cup\{\bot\}$, define $Q:[N]^2\to[N]\cup\{\bot\}$ by retaining $P(i,N-j)$ if its value is smaller than $N$, and setting $Q(i,j)=\bot$ otherwise. Assume $L_0$ is Latin and completes $Q$. Assume $P(d,d)=N$, that this is the unique occurrence of $N$, and that every filled cell with symbol smaller than $N$ satisfies $i<j$. Define
--   $$M(i,j)=\begin{cases}L_0(i,N-j)&i<j,\\N&i=j,\\\bot&i>j.\end{cases}$$
--    Then
--   $$\forall i,j,a\in[N+1],\quad P(i,j)=a\Rightarrow M(i,j)=a.$$
--    This is preservation of filled cells in a partial array, not itself a full completion conclusion.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L2269. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

lemma ProofsInTheBook.Chapter33.smetMainPartial_extends_of_keepLastShrink_completion {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    {L₀ : Fin N → Fin N → Fin N}
    (hL₀ : Completes (smetMainKeepLastShrink P) L₀)
    {d : Fin (N + 1)}
    (hnorm : SmetaniukTriangularNormalized P d (Fin.last N)) :
    ExtendsPartial P (smetMainPartial L₀) := by sorry
