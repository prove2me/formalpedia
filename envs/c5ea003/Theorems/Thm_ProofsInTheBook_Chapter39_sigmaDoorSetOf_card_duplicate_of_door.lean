-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_sigmaDoorSetOf_card_duplicate_of_door
-- name    : ProofsInTheBook.Chapter39.sigmaDoorSetOf_card_duplicate_of_door
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:07:35.23124+00:00
-- url     : https://prove2.me/theorems/621ee1e7-159e-4b1c-9be9-000e4d367126
-- title:
--   Two deletions when an indexed alternating label is duplicated
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). Let $r,m\in\mathbb N$, let $u:[r]\to[m]$ be injective, and let $L:[r+1]\to\{+,-\}\times[m]$. Put $a_j=((-1)^j,u(j))$, $A_u=\{a_j:j\in[r]\}$, $H_u(i)\iff\forall j\in[r],\ \exists t\in[r+1]\setminus\{i\},\ L(t)=a_j$, and $D_u(L)=\{i:H_u(i)\}$. No monotonicity of $u$ is assumed. Let $e\in[r+1]$ and $j\in[r]$. If $H_u(e)$ and $L(e)=a_j$, then
--   $$|D_u(L)|=2.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L1782. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.sigmaDoorSetOf_card_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 2 := by sorry
