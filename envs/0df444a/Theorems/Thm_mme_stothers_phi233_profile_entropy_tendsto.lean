-- Prove2me | Theorems.Thm_mme_stothers_phi233_profile_entropy_tendsto
-- name    : mme_stothers_phi233_profile_entropy_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:33:22.345523+00:00
-- url     : https://prove2.me/theorems/b2745f7e-da51-4a9c-8f56-b2230a61d350
-- title:
--   Continuity of the phi_233 profile entropy under integer rounding
-- statement:
--   Let $A_n,B_n,C_n,D_n$ be sequences of nonnegative integer profile counts such that $A_n/n\to a$, $B_n/n\to b$, $C_n/n\to c$, and $D_n/n\to d$. With $h(x)=-x\log x$ continuously extended by $h(0)=0$, the associated symmetric ten-label entropies converge:
--
--   $$
--   4h\!\left(\frac{A_n}{2n}\right)+2h\!\left(\frac{B_n}{2n}\right)+2h\!\left(\frac{C_n}{2n}\right)+2h\!\left(\frac{D_n}{2n}\right)\longrightarrow 4h\!\left(\frac a2\right)+2h\!\left(\frac b2\right)+2h\!\left(\frac c2\right)+2h\!\left(\frac d2\right).
--   $$
--
--   The result remains valid when some limiting frequencies vanish. It is the analytic bridge that lets exact rounded $\varphi_{233}$ profiles inherit the continuous entropy rate used by the Davie–Stothers asymptotic analysis.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) and Lemma 5.1(v), pp. 360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; continuity uses the standard continuous extension of -x log x at zero.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Order.Field

open Filter

set_option autoImplicit false

theorem mme_stothers_phi233_profile_entropy_tendsto
    (a b c d : ℝ) (A B C D : ℕ → ℕ)
    (hA : Tendsto (fun n : ℕ ↦ (A n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hB : Tendsto (fun n : ℕ ↦ (B n : ℝ) / (n : ℝ)) atTop (nhds b))
    (hC : Tendsto (fun n : ℕ ↦ (C n : ℝ) / (n : ℝ)) atTop (nhds c))
    (hD : Tendsto (fun n : ℕ ↦ (D n : ℝ) / (n : ℝ)) atTop (nhds d)) :
    Tendsto
      (fun n : ℕ ↦
        4 * Real.negMulLog ((A n : ℝ) / ((2 * n : ℕ) : ℝ)) +
          2 * Real.negMulLog ((B n : ℝ) / ((2 * n : ℕ) : ℝ)) +
          2 * Real.negMulLog ((C n : ℝ) / ((2 * n : ℕ) : ℝ)) +
          2 * Real.negMulLog ((D n : ℝ) / ((2 * n : ℕ) : ℝ)))
      atTop
      (nhds
        (4 * Real.negMulLog (a / 2) +
          2 * Real.negMulLog (b / 2) +
          2 * Real.negMulLog (c / 2) +
          2 * Real.negMulLog (d / 2))) := by
  sorry
