-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_signSeqDoor_iff_bad_cut
-- name    : ProofsInTheBook.Chapter39.signSeqDoor_iff_bad_cut
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:08:02.801812+00:00
-- url     : https://prove2.me/theorems/cc8d1cb6-04b7-4275-ab0e-9d7a251b1a00
-- title:
--   A cut characterization of sign-sequence deletion positions
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). Let $k\in\mathbb N$ and let $s:[k+1]\to\{+1,-1\}$. Put $e_j=(-1)^j$ and define $D(s)=\{i\in[k+1]:(\forall j<i,\ s_j=e_j)\land(\forall j>i,\ s_j=-e_j)\}$. For $j\in[k+1]$, define $B(j)\iff s_j=-e_j$. For every $i\in[k+1]$,
--   $$i\in D(s)\quad\Longleftrightarrow\quad(\forall j<i,\ \neg B(j))\land(\forall j>i,\ B(j)).$$
--   There is no restriction on $s_i$.
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L653. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.signSeqDoor_iff_bad_cut {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    signSeqDoor s i ↔
      (∀ j : Fin (k + 1), j < i → ¬ signSeqBad s j) ∧
        (∀ j : Fin (k + 1), i < j → signSeqBad s j) := by sorry
