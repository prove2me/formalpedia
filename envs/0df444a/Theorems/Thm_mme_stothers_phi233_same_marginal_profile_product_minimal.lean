-- Prove2me | Theorems.Thm_mme_stothers_phi233_same_marginal_profile_product_minimal
-- name    : mme_stothers_phi233_same_marginal_profile_product_minimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:26:15.790084+00:00
-- url     : https://prove2.me/theorems/fedfd7be-e3ed-4efb-ba8f-bd700fe82b1c
-- title:
--   The selected phi_233 profile minimizes the type-2 completion product
-- statement:
--   Let $E,H,L>0$ satisfy $E<L$ and $H<L$, and put $\sigma=2H/(2H+L)$ and $\mu=E/(E+L)$. There is a nonnegative normalized profile $(a,b,c,d)$ with marginal equations $$2a+b=\sigma,\qquad a+c=\mu,$$ such that every other nonnegative normalized profile $(a',b',c',d')$ with the same marginals satisfies $$a^{2a}b^bc^cd^d\le (a')^{2a'}(b')^{b'}(c')^{c'}(d')^{d'}.$$ Consequently each quotient of a same-marginal completion product by the selected product is at least one, exactly discharging the nontrivial infimum in Equation (3.6) for the $\varphi_{233}$ case of Lemma 5.1(v).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) on p. 360 and Lemma 5.1(v) on p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

theorem mme_stothers_phi233_same_marginal_profile_product_minimal
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
        a ^ (2 * a) * b ^ b * c ^ c * d ^ d ≤
          a' ^ (2 * a') * b' ^ b' * c' ^ c' * d' ^ d' := by
  sorry
