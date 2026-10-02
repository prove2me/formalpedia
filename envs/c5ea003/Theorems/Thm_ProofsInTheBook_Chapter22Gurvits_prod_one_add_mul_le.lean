-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter22Gurvits_prod_one_add_mul_le
-- name    : ProofsInTheBook.Chapter22Gurvits.prod_one_add_mul_le
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:05:17.832361+00:00
-- url     : https://prove2.me/theorems/35b9be10-2901-491d-8f7c-94d57c290660
-- title:
--   An arithmetic–geometric mean bound for linear factors
-- statement:
--   Let $k\geq1$, let $\lambda_1,\ldots,\lambda_k\geq0$, and let $t\geq0$. Then $$\prod_{i=1}^{k}(1+\lambda_i t)\leq\left(1+\frac{t}{k}\sum_{i=1}^{k}\lambda_i\right)^k.$$
-- source:
--   Repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22Gurvits.lean#L62. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture”, pp. 169–177 (https://doi.org/10.1007/978-3-662-57265-8_24). Auxiliary statements are cited to the repository and are not asserted to be separately numbered book theorems.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22
set_option autoImplicit true
open ProofsInTheBook.Chapter22Gurvits
open scoped BigOperators
open ProofsInTheBook.Chapter22

lemma ProofsInTheBook.Chapter22Gurvits.prod_one_add_mul_le {k : ℕ} (hk : 1 ≤ k) (lam : Fin k → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (t : ℝ) (ht : 0 ≤ t) :
    ∏ i, (1 + lam i * t) ≤ (1 + (∑ i, lam i) * t / k) ^ k := by sorry
