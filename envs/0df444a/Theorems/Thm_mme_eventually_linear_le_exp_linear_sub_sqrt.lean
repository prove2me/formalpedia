-- Prove2me | Theorems.Thm_mme_eventually_linear_le_exp_linear_sub_sqrt
-- name    : mme_eventually_linear_le_exp_linear_sub_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T19:32:47.049548+00:00
-- url     : https://prove2.me/theorems/31271ca2-2159-4b0e-b418-ec320f18063a
-- title:
--   Positive exponential growth absorbs a linear factor and square-root loss
-- statement:
--   Let $a$ and $C$ be nonnegative real constants and let $b$ be positive. Then, for all sufficiently large natural numbers $n$, the positive exponential rate with a square-root loss dominates the linear factor: $$a(n+1) ≤
--   \exp(bn-C\sqrt{n+1}).$$ This is the analytic absorption step used when exponentially many retained tensor blocks incur polynomial grouping losses and Behrend-type $\exp(O(\sqrt n))$ losses.
-- source:
--   Elementary asymptotic estimate used to absorb the explicit subexponential losses in Duan--Wu--Zhou Equation (24), Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3, printed pp. 58--59; https://arxiv.org/abs/2210.10173

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Filter Topology

set_option autoImplicit false

theorem mme_eventually_linear_le_exp_linear_sub_sqrt
    (a b C : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      a * (((n + 1 : ℕ) : ℝ)) ≤
        Real.exp
          (b * (n : ℝ) - C * Real.sqrt (((n + 1 : ℕ) : ℝ))) := by
  sorry
