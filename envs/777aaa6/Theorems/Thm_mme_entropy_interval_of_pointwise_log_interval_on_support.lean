-- Prove2me | Theorems.Thm_mme_entropy_interval_of_pointwise_log_interval_on_support
-- name    : mme_entropy_interval_of_pointwise_log_interval_on_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T17:48:58.701977+00:00
-- url     : https://prove2.me/theorems/7cbdd3da-a377-4fe8-a779-4e3ca5d57109
-- title:
--   Entropy intervals from logarithm intervals on the support alone
-- statement:
--   Let $p_0,\dots,p_{n-1}$ be non-negative reals. Suppose that logarithm brackets are supplied **only on the support**,
--
--   $$0 < p_i \;\Longrightarrow\; \ell_i \le \log p_i \le u_i ,$$
--
--   and that the recorded endpoints vanish off the support, $p_i = 0 \Rightarrow \ell_i = u_i = 0$. Then the entropy is bracketed exactly as before:
--
--   $$\sum_i -(p_i u_i) \;\le\; \sum_i -p_i\log p_i \;\le\; \sum_i -(p_i \ell_i).$$
--
--   A zero cell contributes nothing to any of the three sums — $-0\cdot\log 0 = 0$ by convention and $-0\cdot\ell_i = -0\cdot u_i = 0$ — so a numerical certificate may simply omit it, which is what a sparse distribution's log table does in practice. This is the form used by the beta, quarter and gamma distributions of the DWZ witness, where most cells are empty.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open BigOperators

set_option autoImplicit false

theorem mme_entropy_interval_of_pointwise_log_interval_on_support
    {n : ℕ} (p logLower logUpper : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hzero : ∀ i, p i = 0 → logLower i = 0 ∧ logUpper i = 0)
    (hlog : ∀ i, 0 < p i → logLower i ≤ Real.log (p i) ∧
      Real.log (p i) ≤ logUpper i) :
    (∑ i, -(p i * logUpper i)) ≤
        (∑ i, Real.negMulLog (p i)) ∧
      (∑ i, Real.negMulLog (p i)) ≤
        ∑ i, -(p i * logLower i) := by sorry
