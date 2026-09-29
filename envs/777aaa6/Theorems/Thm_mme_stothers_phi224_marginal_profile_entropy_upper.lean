-- Prove2me | Theorems.Thm_mme_stothers_phi224_marginal_profile_entropy_upper
-- name    : mme_stothers_phi224_marginal_profile_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:26:36.105153+00:00
-- url     : https://prove2.me/theorems/90fd63ce-d74a-4ce8-be2e-92ff03ec75ee
-- title:
--   Finite entropy upper bound for all phi_224 same-marginal words
-- statement:
--   Let $N>0$. The full family $S$ of length-$2N$ words in the nine fine $\varphi_{224}$ types having the prescribed three projected marginals satisfies
--
--   $$
--   |S|\leq (2N+1)^9\exp\!\left(2N\left[2h\!\left(\frac{\alpha}{2N}\right)+4h\!\left(\frac{\beta}{2N}\right)+2h\!\left(\frac{\gamma}{2N}\right)+h\!\left(\frac{2\delta}{2N}\right)\right]\right),
--   $$
--
--   where $h(t)=-t\log t$ with $h(0)=0$. This is a finite, explicit version of the type-2 same-marginal completion estimate: nonsymmetric completions incur only the displayed polynomial histogram factor beyond the exact symmetric entropy rate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the type-2 completion ratio in equations (3.5)--(3.6) and Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_phi224_normalized_same_marginal_entropy_maximum
import Theorems.Thm_mme_finite_word_family_histogram_entropy_upper

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_marginal_profile_entropy_upper
    (N alpha beta gamma delta : ℕ) (hN : 0 < N) :
    (Nat.card
        (MME.StothersFourth.Phi224.MarginalProfileWord
          N alpha beta gamma delta) : ℝ) ≤
      (((2 * N + 1 : ℕ) : ℝ)) ^ 9 *
        Real.exp (((2 * N : ℕ) : ℝ) *
          (2 * Real.negMulLog
              ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
            4 * Real.negMulLog
              ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog
              ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
            Real.negMulLog
              (((2 * delta : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)))) := by
  sorry
