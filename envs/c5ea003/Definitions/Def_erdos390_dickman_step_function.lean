-- Prove2me | Definitions.Def_erdos390_dickman_step_function
-- name    : erdos390_dickman_step_function
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T13:43:22.481291+00:00
-- url     : https://prove2.me/theorems/5d4e072e-c5d1-45bb-836e-9597342d1fe7
-- title:
--   Finite Dickman step function and normalized covariance translate
-- statement:
--   Define the finite method-of-steps approximants on the real line by
--
--   $$\rho_0(x)=1,\qquad \rho_{n+1}(x)=\begin{cases}1&x\le1,\\1-\int_1^x\frac{\rho_n(t-1)}{\max(t,1)}\,dt&x>1.\end{cases}$$
--
--   Set $\rho=\rho_5$, $U=9/2$, and
--
--   $$F(x)=\frac{\rho(U-x)}{\rho(U)}.$$
--
--   The auxiliary functions are the positive denominator $\max(x,1)$ and the delay expression $-\rho(x-1)/x$. These definitions provide the finite Dickman function and its normalized translate used in the conditional covariance kernel. Their regularity and bounds are proved separately.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/DickmanBasic.lean#L19-L464

import Mathlib

/-!
# The Dickman function on the finite range needed for Erdős 390

This file constructs the Dickman function by the method of steps.  No
existence, regularity, positivity, or kernel estimate is assumed as an input.
Only the range up to `5` is needed for the Poisson--Dickman operator at
`U = 9 / 2`.
-/

open Filter Set
open scoped Interval

noncomputable section

namespace Erdos390.Full.DickmanBasic

/-- A globally continuous denominator which agrees with `x` on `[1,∞)`.
It lets every step integrand be defined on all of `ℝ`, while the Dickman
recursion itself only integrates over `[1,x]` with `x > 1`. -/
def safeDenom (x : ℝ) : ℝ := max x 1







/-- Finite method-of-steps approximants.  Successive approximants agree on
successively longer initial intervals. -/
def rhoApprox : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun x =>
      if x ≤ 1 then 1
      else 1 - ∫ t in (1 : ℝ)..x, rhoApprox n (t - 1) / safeDenom t

















/-- The finite Dickman function needed below.  Five method-of-steps stages
are enough on `[0,5]`. -/
def rho : ℝ → ℝ := rhoApprox 5



























 def delayDeriv (x : ℝ) : ℝ := -rho (x - 1) / x











/-- The Dickman parameter used by the Poisson--Dickman bridge. -/
def U : ℝ := (9 : ℝ) / 2





/-- The normalized translate used in the conditional covariance kernel. -/
def F (x : ℝ) : ℝ := rho (U - x) / rho U



































end Erdos390.Full.DickmanBasic


