-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter28_chapter28_erdos_ko_rado
-- name    : ProofsInTheBook.Chapter28.chapter28_erdos_ko_rado
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:08:44.706189+00:00
-- url     : https://prove2.me/theorems/be48fa37-999b-4d3b-af68-8a3cf17fcbc5
-- title:
--   Erdős–Ko–Rado theorem
-- statement:
--   Let $n,r\in\mathbb N$ satisfy $2r\le n$, and let $\mathcal A$ be a finite family of $r$-element subsets of $\operatorname{Fin}(n)$. Assume every pair of members has nonempty intersection, including a member paired with itself. In particular, the empty set cannot be a member. Then
--   $$|\mathcal A|\le {n-1\choose r-1}.$$
--   Subtractions are natural subtractions. No extra hypothesis $r>0$ is inserted into the Lean statement.
--
--   This is a direct use of Mathlib’s Erdős–Ko–Rado inequality, not a separately formalized proof from the book.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 30, “Three famous theorems on finite sets”, pp. 213–217 (https://doi.org/10.1007/978-3-662-57265-8_30). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter28.lean#L37. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter28
open ProofsInTheBook.Chapter28
open Finset

theorem ProofsInTheBook.Chapter28.chapter28_erdos_ko_rado {n r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hr : (𝒜 : Set (Finset (Fin n))).Sized r) (hn : 2 * r ≤ n) :
    𝒜.card ≤ (n - 1).choose (r - 1) := by sorry
