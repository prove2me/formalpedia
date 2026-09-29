-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_integer_profile_rounding
-- name    : mme_stothers_phi233_exact_integer_profile_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:26:13.791172+00:00
-- url     : https://prove2.me/theorems/d4126b08-78d0-4391-a3d0-52e6361d5739
-- title:
--   Exact integer rounding of a feasible phi_233 profile
-- statement:
--   Let $a,b,c,d$ be nonnegative real frequencies satisfying the $\varphi_{233}$ normalization $$2a+b+c+d=1.$$ Then there are nonnegative integer sequences $A_n,B_n,C_n,D_n$ satisfying the exact identity $$2A_n+B_n+C_n+D_n=n$$ for every $n$, while $$A_n/n\to a,\qquad B_n/n\to b,\qquad C_n/n\to c,\qquad D_n/n\to d.$$ This supplies the exact finite multiplicities needed to pass from the real optimizer in Davie--Stothers Lemma 5.1(v) to the integer type profiles used by Lemma 3.3.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 limit construction in Section 3.2, pp. 359--360, and Lemma 5.1(v), p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecificLimits.Basic

open Filter

set_option autoImplicit false

theorem mme_stothers_phi233_exact_integer_profile_rounding
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : 2 * a + b + c + d = 1) :
    ∃ A B C D : ℕ → ℕ,
      (∀ n, 2 * A n + B n + C n + D n = n) ∧
      Tendsto (fun n : ℕ ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a) ∧
      Tendsto (fun n : ℕ ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b) ∧
      Tendsto (fun n : ℕ ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c) ∧
      Tendsto (fun n : ℕ ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d) := by
  sorry
