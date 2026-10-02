-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter28_chapter28_dilworth_lower_bound
-- name    : ProofsInTheBook.Chapter28.chapter28_dilworth_lower_bound
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:09:00.618012+00:00
-- url     : https://prove2.me/theorems/27d733f4-675a-4efb-8e33-d264c0961405
-- title:
--   Antichain lower bound on chain partitions
-- statement:
--   Let $X$ be a finite partially ordered type with decidable equality. Let $A\subseteq X$ be an antichain, and let $\mathcal C$ be a `ChainPartitionOn` of all of $X$: its finite chain parts cover $X$ and distinct parts are disjoint. Then
--   $$|A|\le |\mathcal C|.$$
--
--   This is the antichain lower bound on the number of parts in any chain partition. It does not construct an optimal partition or assert the equality in the full Dilworth theorem.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 30, “Three famous theorems on finite sets”, pp. 213–217 (https://doi.org/10.1007/978-3-662-57265-8_30). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter28.lean#L124. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter28
open ProofsInTheBook.Chapter28
open Finset

theorem ProofsInTheBook.Chapter28.chapter28_dilworth_lower_bound {α : Type*} [Fintype α] [PartialOrder α]
    [DecidableEq α] (A : Finset α) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (𝒞 : ChainPartitionOn (univ : Finset α)) :
    A.card ≤ 𝒞.parts.card := by sorry
