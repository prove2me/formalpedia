-- Prove2me | Theorems.Thm_mme_dwz_common_prime_le_exp_sixteen_length
-- name    : mme_dwz_common_prime_le_exp_sixteen_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:41:16.239984+00:00
-- url     : https://prove2.me/theorems/14681657-1c90-46c6-9541-426c1ea2526e
-- title:
--   Exponential upper bound for the common asymmetric-hashing prime
-- statement:
--   Let d and Q be the two finite collision caps used to choose a common prime p for asymmetric hashing on length-L words over the fifteen Table-2 component labels. If d,Q≤15^L and Bertrand's construction gives p≤2 max{4,8 max{d,Q}}, then p≤exp(16(L+1)). The constant 16 is deliberately coarse and supplies the explicit exponential-prime hypothesis needed to absorb the Behrend loss.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, common-prime choice in Claim 6.8 and the hashing analysis of Section 6.2, printed pp. 53-57; https://arxiv.org/abs/2210.10173

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option autoImplicit false

theorem mme_dwz_common_prime_le_exp_sixteen_length
    (L d Q p : ℕ)
    (hd : d ≤ 15 ^ L) (hQ : Q ≤ 15 ^ L)
    (hp : p ≤ 2 * max 4 (8 * max d Q)) :
    (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) := by
  sorry
