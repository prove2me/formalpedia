-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_smetRectStep_invariant
-- name    : ProofsInTheBook.Chapter33.smetRectStep_invariant
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:06:50.018068+00:00
-- url     : https://prove2.me/theorems/b0612e7f-5ce0-4cd3-a700-1a9b372d177b
-- title:
--   Preservation of the Smetaniuk switching-stage invariant
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. Let $N,t\in\mathbb N$, $L_0:[N]^2\to[N]$, and $R:[N]\times[N+1]\to[N+1]$. For $L_0:[N]^2\to[N]$ and $R:[N]\times[N+1]\to[N+1]$, define $\mathcal I_t(L_0,R)$ by these seven conditions: each row of $R$ is injective; each column $j<N$ is injective; column $N$ is injective on rows $i\ge N-t$; $R(i,N)=N$ for $i<N-t$; $R(i,j)=L_0(i,j)$ for $t<j<N$; $R(i,j)=L_0(i,j)$ for $j<N$ and $i+j<N$; and $R(i,N-i)=N$ for $i\ge N-t$. All rows range over $[N]$, and natural-number subtraction is truncated at zero. For $t+1<N$, put $c=t+1$ and $b=N-(t+1)$. Let $T\subseteq[N]$ be the least set containing $b$ and closed under this rule: if $q\in T$, $r\ge b$, and $R(r,N)=R(q,c)$, then $r\in T$. Define $R^{\prime}$ by interchanging columns $c$ and $N$ in each row of $T$, leaving the other entries unchanged. Assume $t+1<N$ and $\mathcal I_t(L_0,R)$. Then
--   $$\mathcal I_{t+1}(L_0,R^{\prime}).$$
--    No independent Latin assumption on $L_0$ is made; all seven invariant conditions are inputs.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L2615. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

lemma ProofsInTheBook.Chapter33.smetRectStep_invariant {N t : ℕ}
    {L₀ : Fin N → Fin N → Fin N}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)}
    (ht : t + 1 < N)
    (inv : SmetRectStageInvariant L₀ t R) :
    SmetRectStageInvariant L₀ (t + 1) (smetRectStep R t) := by sorry
