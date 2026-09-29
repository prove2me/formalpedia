-- Prove2me | Theorems.Thm_mme_MMObj_tau_value
-- name    : mme_MMObj_tau_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:40:21.692201+00:00
-- url     : https://prove2.me/theorems/9dde2161-8822-4c42-890a-6bf674763d0c
-- title:
--   A matrix-multiplication tensor attains its elementary tau-weight
-- statement:
--   For every matrix-multiplication tensor $\langle n,m,p\rangle$ and every real $\tau$, its tau-value is at least its elementary matrix-product weight: $$V_\tau(\langle n,m,p\rangle)\ge(nmp)^\tau.$$ At each tensor power, the single matrix product $\langle n^N,m^N,p^N\rangle$ is an exact extraction, so the asymptotic witness has no combinatorial loss.
-- source:
--   Immediate from multiplicativity of matrix-multiplication tensors under Kronecker product and the definition of tau-value.

import Definitions.Def_mme_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_MMObj_tau_value
    {K : Type u} [Field K]
    (n m p : ℕ) (tau : ℝ) :
    HasTauValueAtLeast (MMObj K n m p) tau
      (((n * m * p : ℕ) : ℝ) ^ tau) := by
  sorry
