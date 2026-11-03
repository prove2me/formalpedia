-- Prove2me | Theorems.Thm_WordRAM_APSPBridge_real_log_pow_le_rpow
-- name    : WordRAM.APSPBridge.real_log_pow_le_rpow
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-02T20:30:23.701702+00:00
-- url     : https://prove2.me/theorems/bc91b801-2964-4a1e-b35c-beecf72e1c6c
-- title:
--   Polynomial powers of the logarithm are bounded by every positive power
-- statement:
--   For every natural number $m$ and every positive real $\varepsilon$, there is a positive constant $K$ such that for every real $x\ge2$, $$(\log x)^m\le K\,x^{\varepsilon}.$$ Thus every fixed polynomial power of the logarithm grows more slowly than every positive power of $x$. This is the analytic estimate behind absorbing polylogarithmic overhead in runtime-transfer arguments.
-- source:
--   Standard asymptotic estimate $\log^m x=o(x^\varepsilon)$; used in the mission 'Two WordRAM models: equivalence with polylogarithmic overhead' for the fine-grained transfer step.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

theorem WordRAM.APSPBridge.real_log_pow_le_rpow (m : Nat) {ε : ℝ} (hε : 0 < ε) : ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → (Real.log x) ^ m ≤ K * x ^ ε := by sorry
