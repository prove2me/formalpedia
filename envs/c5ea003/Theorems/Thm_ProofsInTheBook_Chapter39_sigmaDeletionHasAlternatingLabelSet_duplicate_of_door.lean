-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_sigmaDeletionHasAlternatingLabelSet_duplicate_of_door
-- name    : ProofsInTheBook.Chapter39.sigmaDeletionHasAlternatingLabelSet_duplicate_of_door
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:07:26.320183+00:00
-- url     : https://prove2.me/theorems/f1d52c2b-ea81-402e-8ab9-48f58cb9f803
-- title:
--   Exchanging equal labels preserves an alternating deletion
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). Let $d\in\mathbb N$, let $L:[d+1]\to\{+,-\}\times[d]$, and put $a_j=((-1)^j,j)$ and $A_d=\{a_j:j\in[d]\}$. For $i\in[d+1]$ write $H(i)$ for $\forall j\in[d],\ \exists t\in[d+1]\setminus\{i\},\ L(t)=a_j$, and put $D_A(L)=\{i:H(i)\}$. Let $e,t\in[d+1]$ and $j\in[d]$. If $H(e)$, $L(e)=a_j$, $t\ne e$, and $L(t)=a_j$, then
--   $$H(t).$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L2479. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.sigmaDeletionHasAlternatingLabelSet_duplicate_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra t : Fin (d + 1)} {k : Fin d}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabel k)
    (htne : t ≠ extra)
    (htlabel : sigmaLabel t = alternatingLabel k) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel t := by sorry
