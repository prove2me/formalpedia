-- Prove2me | Theorems.Thm_mme_asymptotic_sum_inequality_sharp
-- name    : mme_asymptotic_sum_inequality_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:27:50.202721+00:00
-- url     : https://prove2.me/theorems/0ad03124-dd53-49a2-96b0-9b71d5cadcd1
-- title:
--   Sharp real-valued asymptotic sum inequality
-- statement:
--   For any finite family of matrix-multiplication tensors over a field $K$, Schönhage's weighted volume sum is bounded by the exact real asymptotic rank of their direct sum:
--
--   $$\sum_i (n_i m_i p_i)^{\omega_K/3} \le \widetilde R\!\left(\bigoplus_i \langle n_i,m_i,p_i\rangle\right).$$
--
--   Unlike the integer-parameter form of the asymptotic sum inequality, this sharp form retains the exact asymptotic-rank value. It is the form required to compare laser-method extractions with arbitrary real asymptotic-rank bounds.
-- source:
--   A. Schönhage, Partial and Total Matrix Multiplication, SIAM Journal on Computing 10(3), 1981, 434–455; V. Strassen, The asymptotic spectrum of tensors, Journal für die reine und angewandte Mathematik 384 (1988), 102–152.

import Definitions.Def_mme_tensor_bridge
open MME BigOperators
universe u

theorem mme_asymptotic_sum_inequality_sharp
    {K : Type u} [Field K] {k : ℕ} (n m p : Fin k → ℕ) :
    ∑ i, ((n i * m i * p i : ℕ) : ℝ) ^
        (matMulExp_strassen K / 3) ≤
      tensorAsymptoticRank
        (TensorObj.bigAdd (fun i => MMObj K (n i) (m i) (p i))) := by sorry
