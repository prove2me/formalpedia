-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter22Stable_derivative_roots_im_nonpos
-- name    : ProofsInTheBook.Chapter22Stable.derivative_roots_im_nonpos
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:05:29.661424+00:00
-- url     : https://prove2.me/theorems/1099e1fd-2f8f-4724-9d61-8e85618a9b80
-- title:
--   Differentiation preserves the closed lower half-plane root condition
-- statement:
--   Let $p\in\mathbb C[X]$. If every root $z$ in the root multiset of $p$ satisfies $\operatorname{Im}z\leq0$, then every root of $p^{\prime}$ also satisfies $\operatorname{Im}z\leq0$. There is no nonzero or degree assumption. The root multiset of the zero polynomial is empty in the formal convention.
-- source:
--   Repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Stable.lean#L146. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture”, pp. 169–177 (https://doi.org/10.1007/978-3-662-57265-8_24). Auxiliary statements are cited to the repository and are not asserted to be separately numbered book theorems.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22
set_option autoImplicit true
open ProofsInTheBook.Chapter22Stable
open MvPolynomial
open Polynomial

lemma ProofsInTheBook.Chapter22Stable.derivative_roots_im_nonpos (p : Polynomial ℂ)
    (hp : ∀ z ∈ p.roots, z.im ≤ 0) :
    ∀ z ∈ (Polynomial.derivative p).roots, z.im ≤ 0 := by sorry
