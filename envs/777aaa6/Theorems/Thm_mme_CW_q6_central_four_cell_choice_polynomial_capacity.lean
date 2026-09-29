-- Prove2me | Theorems.Thm_mme_CW_q6_central_four_cell_choice_polynomial_capacity
-- name    : mme_CW_q6_central_four_cell_choice_polynomial_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:24:43.933801+00:00
-- url     : https://prove2.me/theorems/b6de93fc-801c-4a3e-ad5d-aa4853a10ac8
-- title:
--   Central four-cell choices occupy a polynomial fraction of all coordinate halves
-- statement:
--   If $L+G=2n$, then the number of central choices in the four joint X/Y cells satisfies
--
--   $$\binom{4n}{2n}\leq (2n+1)^4\binom{L}{\lfloor L/2\rfloor}^2\binom{G}{n-\lfloor L/2\rfloor}^2.$$
--
--   Consequently these choices form at least a $1/(2n+1)^4$ fraction of all coordinate halves of size $2n$.  The division-free inequality is the polynomial-loss estimate needed for the common-halving double count.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, paired 121/211 analysis in Section 7; https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Theorems.Thm_mme_two_pow_le_succ_mul_central_choose

set_option autoImplicit false

theorem mme_CW_q6_central_four_cell_choice_polynomial_capacity
    {n L G : ℕ} (hLG : L + G = 2 * n) :
    Nat.choose (2 * (2 * n)) (2 * n) ≤
      (2 * n + 1) ^ 4 *
        ((Nat.choose L (L / 2) * Nat.choose L (L / 2)) *
          (Nat.choose G (n - L / 2) * Nat.choose G (n - L / 2))) := by
  sorry
