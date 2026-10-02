-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter33_exists_perm_singleton_diagonal_strictly_above
-- name    : ProofsInTheBook.Chapter33.exists_perm_singleton_diagonal_strictly_above
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:05:54.625915+00:00
-- url     : https://prove2.me/theorems/6f5f9c55-994c-47d4-b5df-08b9ece01015
-- title:
--   Moving a distinguished sparse cell onto the diagonal
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. Let $n\in\mathbb N$, let $S\subseteq[n]^2$, and let $e=(e_1,e_2)\in S$. Assume $|S|<n$. There exist permutations $\rho,\kappa$ of $[n]$ and $d\in[n]$ such that
--   $$\rho(e_1)=d=\kappa(e_2),\qquad\forall(i,j)\in S\setminus\{e\},\quad\rho(i)<\kappa(j).$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L1321. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter33
set_option autoImplicit true
open Finset
open Classical
open ProofsInTheBook.Chapter33

theorem ProofsInTheBook.Chapter33.exists_perm_singleton_diagonal_strictly_above {n : ℕ}
    (S : Finset (Fin n × Fin n)) {e : Fin n × Fin n}
    (he : e ∈ S) (hS : S.card < n) :
    ∃ σ τ : Equiv.Perm (Fin n), ∃ d : Fin n,
      σ e.1 = d ∧ τ e.2 = d ∧
        ∀ p ∈ S, p ≠ e → σ p.1 < τ p.2 := by sorry
