-- Prove2me | Theorems.Thm_mme_tau_value_below_base_le_of_asymptoticRank_le
-- name    : mme_tau_value_below_base_le_of_asymptoticRank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:13:25.530446+00:00
-- url     : https://prove2.me/theorems/8dc1d38b-87ac-4f73-96a6-b6edaa360cbb
-- title:
--   Rank bound from every strictly smaller tau-value base
-- statement:
--   Let $T$ be an order-three tensor over a field $K$, and let $R\ge 1$ be an upper bound for its asymptotic tensor rank. Suppose that every real base $V$ in the half-open interval $[1,B)$ is attained by an unrestricted tau-value witness for $T$ at the critical parameter $\tau=\omega_{\mathrm{Strassen}}(K)/3$. Then
--
--   $$
--   B\le R.
--   $$
--
--   This is the endpoint-closure form of the tau-value/rank bridge. It is designed for laser-method estimates that establish every strict lower base below an asymptotic value, without claiming that the limiting base itself is attained with constant-relative accuracy.
-- source:
--   Formal endpoint-closure consequence of the asymptotic sum inequality and the tau-value/rank bridge; compare V. Strassen, Relative bilinear complexity and matrix multiplication, Journal fur die reine und angewandte Mathematik 375/376 (1987), and A. Wigderson and J. Zuiddam, Asymptotic spectra: theory, applications and extensions, arXiv:2305.18068, Sections 2--3; https://arxiv.org/abs/2305.18068

import Definitions.Def_mme_tau_value
import Definitions.Def_mme_omega_strassen
open MME
universe u

theorem mme_tau_value_below_base_le_of_asymptoticRank_le
    {K : Type u} [Field K] {T : TensorObj K 3} {B R : ℝ}
    (hR_one : 1 ≤ R)
    (hR : tensorAsymptoticRank T ≤ R)
    (hbelow : ∀ V : ℝ, 1 ≤ V → V < B →
      HasTauValueAtLeast T (matMulExp_strassen K / 3) V) :
    B ≤ R := by sorry
