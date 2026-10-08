-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_chapter39_unconditional
-- name    : ProofsInTheBook.Chapter39.chapter39_unconditional
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:07:06.345876+00:00
-- url     : https://prove2.me/theorems/f9c12f1b-aa72-4d29-a88e-0f654e2d3d4e
-- title:
--   Kneser–Lovász coloring bounds
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). Let $n,k\in\mathbb N$ satisfy $1\le k$ and $2k\le n$. Let $V=\{A\subseteq[n]:|A|=k\}$, with two distinct vertices adjacent exactly when they are disjoint. Then
--   $$\bigl(\exists C:V\to[n-2k+2],\ \forall A,B\in V,\ A\cap B=\varnothing\Rightarrow C(A)\ne C(B)\bigr)$$
--   $$\land\ \neg\bigl(\exists C:V\to[n-2k+1],\ \forall A,B\in V,\ A\cap B=\varnothing\Rightarrow C(A)\ne C(B)\bigr).$$
--   Thus the chromatic number is $n-2k+2$.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L6317. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.chapter39_unconditional {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) := by sorry
