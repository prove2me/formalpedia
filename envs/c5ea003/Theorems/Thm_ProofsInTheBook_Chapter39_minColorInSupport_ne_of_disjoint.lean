-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter39_minColorInSupport_ne_of_disjoint
-- name    : ProofsInTheBook.Chapter39.minColorInSupport_ne_of_disjoint
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:07:19.389338+00:00
-- url     : https://prove2.me/theorems/efa8a54e-6f21-4594-8e94-fe3f4a9f4470
-- title:
--   Distinct minimum colors on disjoint supports
-- statement:
--   Write $[a]=\{0,\ldots,a-1\}$ for $a\in\mathbb N$ (empty when $a=0$). Let $n,k,q\in\mathbb N$ with $1\le k$, and let $C$ be a proper coloring of the Kneser graph on the $k$-subsets of $[n]$ with colors in $[q]$. For $T\subseteq[n]$ with $|T|\ge k$, define $\mu_C(T)=\min\{C(A):A\subseteq T,\ |A|=k\}$. If $U,V\subseteq[n]$ are disjoint and $|U|,|V|\ge k$, then
--   $$\mu_C(U)\ne\mu_C(V).$$
-- source:
--   Original formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter39.lean#L577. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 43, “The chromatic number of Kneser graphs”, pp. 301–305 (https://doi.org/10.1007/978-3-662-57265-8_43).

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39
set_option autoImplicit true
open ProofsInTheBook.Chapter39

theorem ProofsInTheBook.Chapter39.minColorInSupport_ne_of_disjoint {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    {left right : Finset (Fin n)}
    (hdisj : Disjoint left right)
    (hleft : k ≤ left.card) (hright : k ≤ right.card) :
    minColorInSupport C left hleft ≠ minColorInSupport C right hright := by sorry
