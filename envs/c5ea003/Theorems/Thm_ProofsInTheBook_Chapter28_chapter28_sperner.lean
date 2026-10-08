-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter28_chapter28_sperner
-- name    : ProofsInTheBook.Chapter28.chapter28_sperner
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:08:55.502967+00:00
-- url     : https://prove2.me/theorems/77e2097c-7100-42f9-b742-6ca7c5a26d3f
-- title:
--   Sperner’s theorem
-- statement:
--   Let $X$ be a finite type with decidable equality, let $N=|X|$, and let $\mathcal A$ be a finite family of subsets of $X$. Assume that no distinct members of $\mathcal A$ are comparable by inclusion. Then
--   $$|\mathcal A|\le {N\choose\lfloor N/2\rfloor}.$$
--
--   This is the upper-bound statement of Sperner’s theorem, obtained using the LYM inequality.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 30, “Three famous theorems on finite sets”, pp. 213–217 (https://doi.org/10.1007/978-3-662-57265-8_30). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter28.lean#L50. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter28
open ProofsInTheBook.Chapter28
open Finset

theorem ProofsInTheBook.Chapter28.chapter28_sperner {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 : Finset (Finset α))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) := by sorry
