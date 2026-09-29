-- Prove2me | Theorems.Thm_mme_floor_behrend_polynomial_loss_ge_exp_sqrt
-- name    : mme_floor_behrend_polynomial_loss_ge_exp_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:39:08.699058+00:00
-- url     : https://prove2.me/theorems/c342cbc4-dc6b-4ae2-8632-2c5649bf0e27
-- title:
--   Floor, Behrend, and polynomial losses combine into a square-root-exponential loss
-- statement:
--   Let $n$ be a tensor length, let $p\ge2$ be an integer modulus, and let $D>0$ be a finite denominator. Suppose that for constants $A\ge0$ and $B$ one has
--
--   $$
--   p\le e^{A(n+1)}\qquad\text{and}\qquad D\le e^{B\sqrt{n+1}}.
--   $$
--
--   Then the complete product of the integer half-modulus factor, the explicit Behrend density, and the reciprocal denominator satisfies
--
--   $$
--   \frac{\lfloor p/2\rfloor}{p}\,
--    e^{-4\sqrt{\log\lfloor p/2\rfloor}}\,\frac1D
--   \;\ge\;
--    e^{-(4+4(A+1)+B)\sqrt{n+1}}.
--   $$
--
--   This packages the three finite losses that occur after asymmetric hashing into the single square-root-exponential loss used by the finite form of Equation (25). The estimate is deliberately quantitative and retains the integer floor, rather than replacing it by an asymptotic equivalence.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023 / arXiv:2210.10173, the Salem--Spencer density and polynomial losses in Section 3.10 and the finite loss bookkeeping leading to Equation (25), printed pp. 24-26 and 54-58; elementary analytic normalization of those displayed factors.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Theorems.Thm_mme_nat_div_real_half_lower

open Filter Topology

set_option autoImplicit false

theorem mme_floor_behrend_polynomial_loss_ge_exp_sqrt
    (n p : ℕ) (D A B : ℝ)
    (hA : 0 ≤ A)
    (hp : 2 ≤ p)
    (hpUpper : (p : ℝ) ≤
      Real.exp (A * (((n + 1 : ℕ) : ℝ))))
    (hDpos : 0 < D)
    (hDUpper : D ≤
      Real.exp (B * Real.sqrt (((n + 1 : ℕ) : ℝ)))) :
    Real.exp
        (-(4 + 4 * (A + 1) + B) *
          Real.sqrt (((n + 1 : ℕ) : ℝ))) ≤
      ((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
          Real.exp
            (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ))))) /
        D := by
  sorry
