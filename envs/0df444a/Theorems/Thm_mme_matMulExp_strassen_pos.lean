-- Prove2me | Theorems.Thm_mme_matMulExp_strassen_pos
-- name    : mme_matMulExp_strassen_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-30T19:06:30.634012+00:00
-- url     : https://prove2.me/theorems/fb6805ae-cbf7-4888-87d8-eb121d1c8a55
-- statement:
--   **Strict positivity of the Strassen-form matrix-multiplication exponent.**
--
--   $$0 \;<\; \mathrm{matMulExp\_strassen}\,K.$$
--
--   The Strassen-form exponent $\omega = \mathrm{matMulExp\_strassen}\,K$ is defined as $\inf_n \log_n(\mathrm{strassenRank}(\mathrm{MMTensor}\,n\,n\,n))$ (with $\log_n = \log/\log n$). Even the trivial lower bound $\mathrm{strassenRank}(\mathrm{MMTensor}\,n\,n\,n) \geq n$ for $n \geq 2$ (the matrix product over a field is at least a one-dimensional non-degenerate quadratic form) yields $\omega \geq 1 > 0$.
--
--   **Where it sits.** A small but load-bearing positivity fact in the τ-theorem. The zero-dimension reduction in `mme_sum_inequality` divides the concrete bound into a positive subfamily and a zero-dimension complement; on the complement the summand $(n_i m_i p_i)^{\omega/3} = 0^{\omega/3}$, which equals $0$ precisely because $\omega/3 \neq 0$. This is where `mme_matMulExp_strassen_pos` is used.
-- source:
--   Folklore (a trivial lower bound on ω from $\mathrm{strassenRank}(\mathrm{MM}_{n,n,n}) \geq n^2$).

import Definitions.Def_mme_omega_strassen
open MME
universe u

theorem mme_matMulExp_strassen_pos {K : Type u} [Field K] : 0 < matMulExp_strassen K := by sorry
