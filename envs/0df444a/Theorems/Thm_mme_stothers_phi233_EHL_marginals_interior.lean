-- Prove2me | Theorems.Thm_mme_stothers_phi233_EHL_marginals_interior
-- name    : mme_stothers_phi233_EHL_marginals_interior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:46:14.731562+00:00
-- url     : https://prove2.me/theorems/46bbcbad-2611-4faa-b074-b153e0d3f15e
-- title:
--   Strict interiority of the Davie–Stothers phi_233 marginals
-- statement:
--   Let $E,H,L$ be positive real parameters with $E<L$ and $H<L$, and define the $\varphi_{233}$ marginal ratios
--
--   $$
--   \sigma=\frac{2H}{2H+L},\qquad \mu=\frac{E}{E+L}.
--   $$
--
--   Then
--
--   $$
--   0<\sigma<1,\qquad 0<\mu,\qquad \frac{\sigma}{2}+\mu<1.
--   $$
--
--   Thus the Davie–Stothers parameters lie strictly inside the marginal region required for a positive stationary $\varphi_{233}$ profile. This turns the paper's coarse inequalities $E,H<L$ into the exact hypotheses used by the critical-profile existence theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (5.1) and Lemma 5.1(v), pp. 364–366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic

set_option autoImplicit false

theorem mme_stothers_phi233_EHL_marginals_interior
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    0 < sigma ∧ 0 < mu ∧ sigma < 1 ∧ sigma / 2 + mu < 1 := by
  sorry
