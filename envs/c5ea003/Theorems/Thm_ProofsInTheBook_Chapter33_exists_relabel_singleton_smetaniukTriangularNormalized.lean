-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_exists_relabel_singleton_smetaniukTriangularNormalized
-- name    : ProofsInTheBook.Chapter33.exists_relabel_singleton_smetaniukTriangularNormalized
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:06:01.505469+00:00
-- url     : https://prove2.me/theorems/19d7f1c9-0067-488a-9390-fe4d14810852
-- title:
--   Triangular normalization of a uniquely occurring symbol
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. Let $N\in\mathbb N$ and let $P$ have order $N+1$. Assume $|F(P)|\le N$ and a symbol $a\in[N+1]$ occurs exactly once. There exist permutations $\rho,\kappa,\sigma$ of $[N+1]$ and $d\in[N+1]$ such that $Q(i,j)=\sigma(P(\rho(i),\kappa(j)))$, with empty cells preserved, satisfies
--   $$Q(d,d)=N,\qquad Q(i,j)=N\Rightarrow(i,j)=(d,d),\qquad Q(i,j)=s\in[N]\Rightarrow i<j.$$
--    No partial Latin condition is assumed.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L1507. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

theorem ProofsInTheBook.Chapter33.exists_relabel_singleton_smetaniukTriangularNormalized {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    {a : Fin (N + 1)}
    (hcard : (filledCells P).card ≤ N)
    (hone : SymbolOccursExactlyOnce P a) :
    ∃ rowPerm colPerm symPerm : Equiv.Perm (Fin (N + 1)), ∃ d : Fin (N + 1),
      SmetaniukTriangularNormalized
        (relabelPartial rowPerm colPerm symPerm P) d (Fin.last N) := by sorry
