-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_signSeqDoor_iff_remove_altPos
-- name    : ProofsInTheBook.Chapter39.signSeqDoor_iff_remove_altPos
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:07:45.97973+00:00
-- url     : https://prove2.me/theorems/00ca8597-7d77-48fb-a9e9-a6dfae20e1a0
-- title:
--   Deleting a sign-sequence cut produces positive-first alternation
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). Let $k\in\mathbb N$ and let $s:[k+1]\to\{+1,-1\}$. Put $e_j=(-1)^j$ and define $D(s)=\{i\in[k+1]:(\forall j<i,\ s_j=e_j)\land(\forall j>i,\ s_j=-e_j)\}$. For $i\in[k+1]$, let $\delta_i:[k]\to[k+1]$ be the increasing injection omitting $i$, namely $\delta_i(a)=a$ for $a<i$ and $a+1$ otherwise. Then
--   $$i\in D(s)\quad\Longleftrightarrow\quad\forall a\in[k],\ s_{\delta_i(a)}=(-1)^a.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L679. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.signSeqDoor_iff_remove_altPos {k : ℕ} (s : Fin (k + 1) → Bool)
    (i : Fin (k + 1)) :
    signSeqDoor s i ↔ signSeqAltPos (fun a : Fin k => s (i.succAbove a)) := by sorry
