-- Prove2me | Theorems.Thm_mme_exp_log_two_entropyBits_eq_prod_rpow
-- name    : mme_exp_log_two_entropyBits_eq_prod_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:40:41.593867+00:00
-- url     : https://prove2.me/theorems/4ae15e53-9d74-4fd8-a0e9-da478609b3fc
-- title:
--   Exponential Shannon entropy as a weighted reciprocal product
-- statement:
--   Let $p$ be a strictly positive real-valued function on a finite set. Then exponentiating its base-two Shannon entropy gives the weighted reciprocal geometric product $$\exp((\log 2)H_2(p))=\prod_i p_i^{-p_i}.$$ This identity is useful for translating entropy-form multinomial bounds into the product form used by laser-method rate formulas.
-- source:
--   Standard finite Shannon-entropy identity, obtained directly from H_2(p)=-(1/log 2) sum_i p_i log p_i. Used in the multinomial asymptotics underlying the Coppersmith--Winograd and Davie--Stothers laser methods.

import Definitions.Def_mme_modern_entropy_data

open BigOperators

set_option autoImplicit false

theorem mme_exp_log_two_entropyBits_eq_prod_rpow
    {D : Type*} [Fintype D]
    (p : D → ℝ) (hp : ∀ i, 0 < p i) :
    Real.exp (Real.log 2 * mme_modern_entropyBits p) =
      ∏ i, Real.rpow (p i) (-p i) := by
  sorry
