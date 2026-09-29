-- Prove2me | Theorems.Thm_mme_stothers_phi233_full_same_marginal_entropy_maximum
-- name    : mme_stothers_phi233_full_same_marginal_entropy_maximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:13:28.66938+00:00
-- url     : https://prove2.me/theorems/bbc8f12b-67d5-4b19-83a4-23a75c6b3250
-- title:
--   Full same-marginal entropy maximum for phi_233
-- statement:
--   For positive $E,H$ with $E,H<L$, put $\sigma=2H/(2H+L)$ and $\mu=E/(E+L)$. There is a nonnegative symmetric profile $(a,b,c,d)$ satisfying $2a+b+c+d=1$, $2a+b=\sigma$, and $a+c=\mu$ such that every nonnegative normalized profile $x$ on the ten ordered $\varphi_{233}$ types with the same relevant marginals obeys\n\n$$\n\sum_{r=0}^{9}-x_r\log x_r\;\le\;4h(a/2)+2h(b/2)+2h(c/2)+2h(d/2),\qquad h(t)=-t\log t.\n$$\n\nThus the symmetric Davie--Stothers profile is an entropy maximizer over the entire, potentially nonsymmetric, same-marginal completion fibre. This is the exceptional convexity step needed to compare the ambient family $S$ with the exact target family $S_0$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 symmetry and entropy argument around Equation (3.6), pp. 359--360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_same_marginal_entropy_minimal
import Theorems.Thm_mme_stothers_phi233_orbit_entropy_symmetrization
import Theorems.Thm_mme_stothers_phi233_orbit_average_constraints

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mme_stothers_phi233_full_same_marginal_entropy_maximum
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    ∃ a b c d : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      2 * a + b + c + d = 1 ∧
      2 * a + b = sigma ∧ a + c = mu ∧
      ∀ x : Fin 10 → ℝ,
        (∀ r, 0 ≤ x r) →
        (∑ r : Fin 10, x r) = 1 →
        x 0 + x 1 + x 2 = sigma / 2 →
        x 7 + x 8 + x 9 = sigma / 2 →
        x 3 + x 7 = mu / 2 →
        x 2 + x 6 = mu / 2 →
        x 6 + x 9 = mu / 2 →
        x 0 + x 3 = mu / 2 →
        (∑ r : Fin 10, Real.negMulLog (x r)) ≤
          4 * Real.negMulLog (a / 2) +
          2 * Real.negMulLog (b / 2) +
          2 * Real.negMulLog (c / 2) +
          2 * Real.negMulLog (d / 2) := by
  sorry
