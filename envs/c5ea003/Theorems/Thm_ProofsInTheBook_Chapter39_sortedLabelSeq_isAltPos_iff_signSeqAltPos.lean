-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_sortedLabelSeq_isAltPos_iff_signSeqAltPos
-- name    : ProofsInTheBook.Chapter39.sortedLabelSeq_isAltPos_iff_signSeqAltPos
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:07:37.175816+00:00
-- url     : https://prove2.me/theorems/2fbfdf02-f629-4551-b9ee-f160e7b9f47c
-- title:
--   Alternation of a label sequence with strictly increasing indices
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). A signed label on $[m]$ is a pair $(\varepsilon,j)$ with $\varepsilon\in\{+,-\}$ and $j\in[m]$; negation reverses its sign. For a sequence $M:[\ell]\to\{+,-\}\times[m]$, write $\operatorname{Alt}_+(M)$ when there exists a strictly increasing $u:[\ell]\to[m]$ such that $\operatorname{im}M=\{((-1)^a,u(a)):a\in[\ell]\}$, and define $\operatorname{Alt}_-(M)$ by reversing all these signs. Here $(-1)^a$ denotes the positive sign for even $a$. These predicates concern the label set ordered by index, not the input order. Let $k,m\in\mathbb N$, let $u:[k]\to[m]$ be strictly increasing, let $s:[k]\to\{+1,-1\}$, and let $L:[k]\to\{+,-\}\times[m]$ satisfy $L(a)=(s_a,u(a))$ for every $a\in[k]$. Then
--   $$\operatorname{Alt}_+(L)\quad\Longleftrightarrow\quad\forall a\in[k],\ s_a=(-1)^a.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L1058. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.sortedLabelSeq_isAltPos_iff_signSeqAltPos {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {sgn : Fin k → Bool} {L : Fin k → SignedLabel m}
    (hL : ∀ a : Fin k, L a = { positive := sgn a, index := idx a }) :
    IsAltPosLabelSeq L ↔ signSeqAltPos sgn := by sorry
