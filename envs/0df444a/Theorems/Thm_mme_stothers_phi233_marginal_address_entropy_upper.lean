-- Prove2me | Theorems.Thm_mme_stothers_phi233_marginal_address_entropy_upper
-- name    : mme_stothers_phi233_marginal_address_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:27:01.525057+00:00
-- url     : https://prove2.me/theorems/55586a69-2c6d-4e1f-9bea-019ab6932e2e
-- title:
--   Entropy upper bound for the full phi_233 same-marginal family
-- statement:
--   For every nonempty length-$2N$ family of $\varphi_{233}$ address words with the exact Davie--Stothers mode marginals, the total number of same-marginal completions is at most a degree-ten polynomial times the exponential of the maximizing ten-label entropy. The witnesses $a,b,c,d$ lie in the symmetric marginal fibre. Thus the formal bound is $|S| \le (2N+1)^{10}\exp(2N T)$, where $T=4h(a/2)+2h(b/2)+2h(c/2)+2h(d/2)$ and $h(x)=-x\log x$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), same-marginal completion count and the entropy maximization surrounding Equation (3.6), pp. 359--360 and 363, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_phi233_pattern_injective
import Theorems.Thm_mme_stothers_phi233_full_same_marginal_entropy_maximum
import Theorems.Thm_mme_stothers_phi233_integer_histogram_normalization
import Theorems.Thm_mme_stothers_phi233_marginal_address_label_histogram
import Theorems.Thm_mme_finite_word_family_histogram_entropy_upper

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mme_stothers_phi233_marginal_address_entropy_upper
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L)
    (hsigma : ((2 * alpha + beta : ℕ) : ℝ) / (N : ℝ) =
      2 * H / (2 * H + L))
    (hmu : ((alpha + gamma : ℕ) : ℝ) / (N : ℝ) =
      E / (E + L)) :
    ∃ a b c d : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      2 * a + b + c + d = 1 ∧
      2 * a + b = 2 * H / (2 * H + L) ∧
      a + c = E / (E + L) ∧
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        (((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
          Real.exp (((2 * N : ℕ) : ℝ) *
            (4 * Real.negMulLog (a / 2) +
              2 * Real.negMulLog (b / 2) +
              2 * Real.negMulLog (c / 2) +
              2 * Real.negMulLog (d / 2))) := by
  sorry
