-- Prove2me | Theorems.Thm_mme_entropy_interval_of_pointwise_log_interval
-- name    : mme_entropy_interval_of_pointwise_log_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T17:46:24.744629+00:00
-- url     : https://prove2.me/theorems/b9e1c354-43e9-4e46-91ab-038d2ca9f897
-- title:
--   Certified logarithm intervals give certified entropy intervals
-- statement:
--   Let $p_0,\dots,p_{n-1}$ be non-negative reals and suppose each $\log p_i$ is bracketed,
--
--   $$\ell_i \;\le\; \log p_i \;\le\; u_i .$$
--
--   Then the entropy expression $\sum_i -p_i\log p_i$ is bracketed by the two sums obtained from the *opposite* endpoints:
--
--   $$\sum_i -(p_i u_i) \;\le\; \sum_i -p_i\log p_i \;\le\; \sum_i -(p_i \ell_i).$$
--
--   The orientation is the whole point: because each term carries a minus sign, an **upper** bound on a logarithm gives a **lower** bound on the entropy, and conversely. Multiplying $\ell_i \le \log p_i \le u_i$ by $p_i \ge 0$ preserves the inequalities, negating reverses them, and summing over the finite index set preserves them again.
--
--   The consequence is that a finite entropy expression needs no transcendental arithmetic once every probability comes with a certified rational logarithm interval: the entropy interval is then a pair of finite sums of products.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open BigOperators

set_option autoImplicit false

theorem mme_entropy_interval_of_pointwise_log_interval
    {n : ℕ} (p logLower logUpper : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hlog : ∀ i, logLower i ≤ Real.log (p i) ∧
      Real.log (p i) ≤ logUpper i) :
    (∑ i, -(p i * logUpper i)) ≤
        (∑ i, Real.negMulLog (p i)) ∧
      (∑ i, Real.negMulLog (p i)) ≤
        ∑ i, -(p i * logLower i) := by sorry
