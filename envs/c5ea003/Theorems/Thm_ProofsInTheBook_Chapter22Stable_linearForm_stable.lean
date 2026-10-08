-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter22Stable_linearForm_stable
-- name    : ProofsInTheBook.Chapter22Stable.linearForm_stable
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:05:38.169336+00:00
-- url     : https://prove2.me/theorems/b727007a-763b-47f4-b563-2bc95319189d
-- title:
--   A nonnegative linear form with positive total weight is real stable
-- statement:
--   Let $m\geq0$ and let $C_1,\ldots,C_m\in\mathbb R$ satisfy $C_j\geq0$ for every j and $\sum_j C_j>0$. Then the linear polynomial $$p(x)=\sum_{j=1}^{m}C_jx_j$$ is real stable: $p(z)\ne0$ whenever all coordinates have strictly positive imaginary part. The positive-sum hypothesis excludes $m=0$ and the zero form.
-- source:
--   Repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Stable.lean#L41. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture”, pp. 169–177 (https://doi.org/10.1007/978-3-662-57265-8_24). Auxiliary statements are cited to the repository and are not asserted to be separately numbered book theorems.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22
set_option autoImplicit true
open ProofsInTheBook.Chapter22Stable
open MvPolynomial

lemma ProofsInTheBook.Chapter22Stable.linearForm_stable {m : ℕ} (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hpos : 0 < ∑ j, C j) :
    RealStable (∑ j, MvPolynomial.C (C j) * (X j : MvPolynomial (Fin m) ℝ)) := by sorry
