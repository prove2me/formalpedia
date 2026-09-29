-- Prove2me | Theorems.Thm_mme_strassen_lt_three_mul_of_tau_value_surplus
-- name    : mme_strassen_lt_three_mul_of_tau_value_surplus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:52:20.075189+00:00
-- url     : https://prove2.me/theorems/3a15a31a-417d-45d8-bc23-bbd048562fcb
-- title:
--   A strict fixed-tau value surplus forces a strict exponent bound
-- statement:
--   Let $T$ be an order-three tensor. Suppose its asymptotic rank is at most $R\ge0$, it has tau-value at least $V\ge1$ at a fixed parameter $\tau>0$, and $V>R$. Then the Strassen-form matrix-multiplication exponent satisfies
--
--   $$
--   \omega_K^{\mathrm{Str}}<3\tau.
--   $$
--
--   Indeed, if $\tau\le\omega_K^{\mathrm{Str}}/3$, tau-value monotonicity transports the fixed-parameter witness to parameter $\omega_K^{\mathrm{Str}}/3$. The proved tau-value/rank bridge would then give $V\le R$, contradicting the strict surplus. This statement contains no exponent bound among its hypotheses.
-- source:
--   A direct fixed-parameter consequence of Schönhage's asymptotic sum inequality and the asymptotic-rank formulation of Strassen's tensor value; see A. Schönhage, Partial and Total Matrix Multiplication, SIAM J. Comput. 10(3), 1981, and Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Theorem 3.2.

import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_tau_value_le_of_asymptoticRank_le

open MME BigOperators Filter

universe u

theorem mme_strassen_lt_three_mul_of_tau_value_surplus
    {K : Type u} [Field K] {T : TensorObj K 3} {tau V R : ℝ}
    (htau : 0 < tau) (hV_one : 1 ≤ V) (hR_nonneg : 0 ≤ R)
    (hR : tensorAsymptoticRank T ≤ R)
    (hV : HasTauValueAtLeast T tau V)
    (hsurplus : R < V) :
    matMulExp_strassen K < 3 * tau := by sorry
