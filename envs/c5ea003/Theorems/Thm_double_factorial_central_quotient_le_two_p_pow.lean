-- Prove2me | Theorems.Thm_double_factorial_central_quotient_le_two_p_pow
-- name    : double_factorial_central_quotient_le_two_p_pow
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T15:51:54.412284+00:00
-- url     : https://prove2.me/theorems/6d54f4ea-dc11-4a28-a383-aeb0e79e5afc
-- statement:
--   The central double-factorial quotient is bounded by $(2p)^p$: $\dfrac{(2p)!}{2^p\,p!} \le (2p)^p$ for every natural number $p$. Equivalently $(2p-1)!! \le (2p)^p$. This is the elementary Gaussian-moment constant bound (the $2p$-th moment of a standard normal is $(2p-1)!!$), proved by induction using the recurrence $\frac{(2(p+1))!}{2^{p+1}(p+1)!} = \frac{(2p)!}{2^p p!}\cdot(2p+1)$ and monotonicity of $x\mapsto x^p$.
-- source:
--   Tropp 2015 (An Introduction to Matrix Concentration Inequalities) Thm 4.1; Gaussian moment identity (2p-1)!!.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

theorem double_factorial_central_quotient_le_two_p_pow (p : ℕ) :
    ((Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ))) ≤ (2 * p : ℝ) ^ p := by sorry
