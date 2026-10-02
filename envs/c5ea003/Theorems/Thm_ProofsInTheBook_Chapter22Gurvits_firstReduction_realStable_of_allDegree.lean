-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter22Gurvits_firstReduction_realStable_of_allDegree
-- name    : ProofsInTheBook.Chapter22Gurvits.firstReduction_realStable_of_allDegree
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:05:18.062455+00:00
-- url     : https://prove2.me/theorems/e2763739-ada7-4ee3-8bb9-13fe7178ea84
-- title:
--   Real stability survives first reduction under full coefficient positivity
-- statement:
--   Let $m\geq1$, and let $p\in\mathbb R[x_0,\ldots,x_m]$ be homogeneous of degree $m+1$. Assume every coefficient of $p$ is nonnegative and the coefficient of every monomial of total degree $m+1$ is strictly positive. Assume also that $p(z)\ne0$ whenever all coordinates of $z\in\mathbb C^{m+1}$ have strictly positive imaginary part. Then the polynomial $[x_0^1]p$ in the remaining $m$ variables is real stable in the same sense. Here $[x_0^1]p$ is equivalently $(\partial p/\partial x_0)|_{x_0=0}$.
-- source:
--   Repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Gurvits.lean#L1241. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture”, pp. 169–177 (https://doi.org/10.1007/978-3-662-57265-8_24). Auxiliary statements are cited to the repository and are not asserted to be separately numbered book theorems.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22
set_option autoImplicit true
open ProofsInTheBook.Chapter22Gurvits
open scoped BigOperators
open ProofsInTheBook.Chapter22

lemma ProofsInTheBook.Chapter22Gurvits.firstReduction_realStable_of_allDegree {m : ℕ} (hm : 1 ≤ m)
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hp : AllDegreeCoefficientsPositive (m + 1) p)
    (hhom : p.IsHomogeneous (m + 1))
    (hstable : ProofsInTheBook.Chapter22Stable.RealStable p) :
    ProofsInTheBook.Chapter22Stable.RealStable (firstReduction p) := by sorry
