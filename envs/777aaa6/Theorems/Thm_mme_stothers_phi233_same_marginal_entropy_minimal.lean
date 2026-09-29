-- Prove2me | Theorems.Thm_mme_stothers_phi233_same_marginal_entropy_minimal
-- name    : mme_stothers_phi233_same_marginal_entropy_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:19:28.164165+00:00
-- url     : https://prove2.me/theorems/7b33379b-e100-429b-ac05-7ee0013d6c0f
-- title:
--   The selected phi_233 profile minimizes entropy cost on its marginal fiber
-- statement:
--   Let $E,H,L>0$ satisfy $E<L$ and $H<L$, and set $\sigma=2H/(2H+L)$ and $\mu=E/(E+L)$. There are nonnegative frequencies $a,b,c,d$ such that $$2a+b+c+d=1,\qquad 2a+b=\sigma,\qquad a+c=\mu,$$ and, among all nonnegative profiles $(a',b',c',d')$ with those same normalization and marginal equations, $$\log(a^{2a}b^bc^cd^d)\le \log((a')^{2a'}(b')^{b'}(c')^{c'}(d')^{d'}),$$ with the continuous convention $0\log 0=0$. This is the exact same-marginal minimization required in the nontrivial $\varphi_{233}$ fiber of Davie--Stothers Lemma 5.1(v); it makes the profile-completion factor in their type-2 estimate at least one.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) on p. 360 and Lemma 5.1(v) on p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false

theorem mme_stothers_phi233_same_marginal_entropy_minimal
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    ∃ a b c d : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      2 * a + b + c + d = 1 ∧
      2 * a + b = sigma ∧ a + c = mu ∧
      ∀ a' b' c' d' : ℝ,
        0 ≤ a' → 0 ≤ b' → 0 ≤ c' → 0 ≤ d' →
        2 * a' + b' + c' + d' = 1 →
        2 * a' + b' = sigma → a' + c' = mu →
        (-2 * Real.negMulLog a - Real.negMulLog b -
            Real.negMulLog c - Real.negMulLog d) ≤
          (-2 * Real.negMulLog a' - Real.negMulLog b' -
            Real.negMulLog c' - Real.negMulLog d') := by
  sorry
