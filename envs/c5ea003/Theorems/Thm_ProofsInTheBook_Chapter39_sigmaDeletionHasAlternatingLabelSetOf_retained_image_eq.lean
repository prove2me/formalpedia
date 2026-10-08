-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
-- name    : ProofsInTheBook.Chapter39.sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:07:14.27458+00:00
-- url     : https://prove2.me/theorems/0b1544ea-6deb-4d1a-9a02-a3be9509e8aa
-- title:
--   Retained label image for an indexed alternating deletion
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). Let $r,m\in\mathbb N$, let $u:[r]\to[m]$ be injective, and let $L:[r+1]\to\{+,-\}\times[m]$. Put $a_j=((-1)^j,u(j))$, $A_u=\{a_j:j\in[r]\}$, $H_u(i)\iff\forall j\in[r],\ \exists t\in[r+1]\setminus\{i\},\ L(t)=a_j$, and $D_u(L)=\{i:H_u(i)\}$. No monotonicity of $u$ is assumed. For every $e\in[r+1]$, if $H_u(e)$, then
--   $$\{L(t):t\in[r+1]\setminus\{e\}\}=A_u.$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39Tucker.lean#L1743. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem ProofsInTheBook.Chapter39.sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetOf idx := by sorry
