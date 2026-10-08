-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_signSeqDoorSet_card_le_two
-- name    : ProofsInTheBook.Chapter39.signSeqDoorSet_card_le_two
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:07:29.55881+00:00
-- url     : https://prove2.me/theorems/4a9fd42a-c221-4be2-9d2a-20acb63787da
-- title:
--   At most two alternating deletions in a sign sequence
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). Let $k\in\mathbb N$ and let $s:[k+1]\to\{+1,-1\}$. Put $e_j=(-1)^j$ and define $D(s)=\{i\in[k+1]:(\forall j<i,\ s_j=e_j)\land(\forall j>i,\ s_j=-e_j)\}$. Then
--   $$|D(s)|\le2.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L755. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.signSeqDoorSet_card_le_two {k : ℕ} (s : Fin (k + 1) → Bool) :
    (signSeqDoorSet s).card ≤ 2 := by sorry
