-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_signSeqDeletionParity
-- name    : ProofsInTheBook.Chapter39.signSeqDeletionParity
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:07:52.544504+00:00
-- url     : https://prove2.me/theorems/35baadbb-2127-49eb-909e-7ced56aa7506
-- title:
--   Parity of alternating deletions in a sign sequence
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). Let $k\in\mathbb N$ and let $s:[k+1]\to\{+1,-1\}$. Put $e_j=(-1)^j$ and define $D(s)=\{i\in[k+1]:(\forall j<i,\ s_j=e_j)\land(\forall j>i,\ s_j=-e_j)\}$. Then
--   $$|D(s)|\text{ is odd}\quad\Longleftrightarrow\quad(\forall j\in[k+1],\ s_j=e_j)\ \lor\ (\forall j\in[k+1],\ s_j=-e_j).$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L915. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.signSeqDeletionParity {k : ℕ} (s : Fin (k + 1) → Bool) :
    Odd (signSeqDoorSet s).card ↔ signSeqAltPos s ∨ signSeqAltNeg s := by sorry
