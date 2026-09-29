-- Prove2me | Theorems.Thm_mme_DWZ_q6_square_fixed_tau_endpoint_23747_kron
-- name    : mme_DWZ_q6_square_fixed_tau_endpoint_23747_kron
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:57:42.193404+00:00
-- url     : https://prove2.me/theorems/ba0b6847-5574-497e-b690-05d1a5ac576b
-- title:
--   The literal q=6 CW square certificate implies omega below 2.3747
-- statement:
--   Let $K$ be any field. Suppose the literal tensor square $CW_6\otimes CW_6$ has tau-value at least
--
--   $$
--   \frac{640001}{10000}=64.0001
--   $$
--
--   at the fixed parameter $\tau=23747/30000$. Then the Strassen-form matrix-multiplication exponent satisfies
--
--   $$
--   \omega_K^{\mathrm{Str}}<\frac{23747}{10000}=2.3747.
--   $$
--
--   The existing tensor-square rank theorem gives $\widetilde R(CW_6\otimes CW_6)\le64$ directly for this exact object. The assumed value is strictly above the rank budget, so tau-monotonicity and the asymptotic sum inequality force the displayed strict exponent bound. The premise contains no exponent conclusion and is exactly the fixed-parameter certificate that the asymmetric-hashing extraction must supply.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Theorem 3.2 and the q=6 second-power specialization in Section 6.3 and Table 2; https://arxiv.org/abs/2210.10173.

import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_CW_square_asymptoticRank_le
import Theorems.Thm_mme_strassen_lt_three_mul_of_tau_value_surplus

open MME BigOperators Filter

universe u

theorem mme_DWZ_q6_square_fixed_tau_endpoint_23747_kron
    {K : Type u} [Field K]
    (hV : HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6))
      (23747 / 30000) (640001 / 10000)) :
    matMulExp_strassen K < 23747 / 10000 := by sorry
