-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter22Gurvits_univariate_gurvits_factored
-- name    : ProofsInTheBook.Chapter22Gurvits.univariate_gurvits_factored
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:05:24.676846+00:00
-- url     : https://prove2.me/theorems/97c6e62d-16aa-481e-9ee6-5e19fd492142
-- title:
--   A factored univariate Gurvits inequality
-- statement:
--   Let $k\geq2$, $c\geq0$, and $C\in\mathbb R$. Let $\lambda_1,\ldots,\lambda_k\geq0$ with $S=\sum_i\lambda_i>0$. Suppose that for every real $t>0$, $$Ct\leq c\prod_{i=1}^{k}(1+\lambda_i t).$$ Then $$\left(\frac{k-1}{k}\right)^{k-1}C\leq cS.$$ No sign restriction on $C$ and no strict positivity requirement on $c$ is imposed.
-- source:
--   Repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Gurvits.lean#L115. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture”, pp. 169–177 (https://doi.org/10.1007/978-3-662-57265-8_24). Auxiliary statements are cited to the repository and are not asserted to be separately numbered book theorems.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22
set_option autoImplicit true
open ProofsInTheBook.Chapter22Gurvits
open scoped BigOperators
open ProofsInTheBook.Chapter22

lemma ProofsInTheBook.Chapter22Gurvits.univariate_gurvits_factored {k : ℕ} (hk : 2 ≤ k) (c C : ℝ) (lam : Fin k → ℝ)
    (hc : 0 ≤ c) (hlam : ∀ i, 0 ≤ lam i) (hS : 0 < ∑ i, lam i)
    (hbound : ∀ t : ℝ, 0 < t → C * t ≤ c * ∏ i, (1 + lam i * t)) :
    G k * C ≤ c * ∑ i, lam i := by sorry
