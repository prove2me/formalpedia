-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_labelSeq_deletionParity_of_not_injective_of_noOpposite
-- name    : ProofsInTheBook.Chapter39.labelSeq_deletionParity_of_not_injective_of_noOpposite
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:07:16.464807+00:00
-- url     : https://prove2.me/theorems/f9831e02-4b35-4042-a196-0af3d6844df3
-- title:
--   Even alternating-deletion count for a noninjective label sequence
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). A signed label on $[m]$ is a pair $(\varepsilon,j)$ with $\varepsilon\in\{+,-\}$ and $j\in[m]$; negation reverses its sign. For a sequence $M:[\ell]\to\{+,-\}\times[m]$, write $\operatorname{Alt}_+(M)$ when there exists a strictly increasing $u:[\ell]\to[m]$ such that $\operatorname{im}M=\{((-1)^a,u(a)):a\in[\ell]\}$, and define $\operatorname{Alt}_-(M)$ by reversing all these signs. Here $(-1)^a$ denotes the positive sign for even $a$. These predicates concern the label set ordered by index, not the input order. Let $k,m\in\mathbb N$ and $L:[k+1]\to\{+,-\}\times[m]$. Assume $L$ is not injective and $L(i)\ne-L(j)$ for all $i,j\in[k+1]$. Let $L^{\widehat i}$ be the sequence obtained by deleting position $i$ and retaining the order of the other entries. Then
--   $$2\mid|\{i\in[k+1]:\operatorname{Alt}_+(L^{\widehat i})\}|,\qquad\neg\operatorname{Alt}_+(L),\qquad\neg\operatorname{Alt}_-(L).$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L2024. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.labelSeq_deletionParity_of_not_injective_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hnot : ¬ Function.Injective L)
    (_hno : NoOppositeLabelSeq L) :
    Even (labelSeqAltPosDeletionSet L).card ∧
      ¬ IsAltPosLabelSeq L ∧ ¬ IsAltNegLabelSeq L := by sorry
