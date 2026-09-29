-- Prove2me | Theorems.Thm_mme_stothers_phi233_integer_histogram_normalization
-- name    : mme_stothers_phi233_integer_histogram_normalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:15:28.887485+00:00
-- url     : https://prove2.me/theorems/c23d7176-8be2-4baa-9990-9f7d5f1fb2ab
-- title:
--   Normalize phi_233 integer histograms to the entropy fibre
-- statement:
--   Let $w_0,\ldots,w_9$ be nonnegative integer counts with total $2N$. Assume the six selected marginal identities of the $\varphi_{233}$ profile: the two outer first-mode sums equal $2\alpha+\beta$, and the four selected second- and third-mode sums equal $\alpha+\gamma$. For $p_r=w_r/(2N)$, $\sigma=(2\alpha+\beta)/N$, and $\mu=(\alpha+\gamma)/N$, the normalized profile is nonnegative, has total mass one, and satisfies exactly the six real marginal equations used by the orbit-averaging entropy theorem. This is the exact adapter from finite histograms to the Davie--Stothers entropy fibre.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 profile equations preceding Equation (3.6), pp. 359--360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_integer_histogram_normalization
    (N alpha beta gamma : ℕ) (hN : 0 < N)
    (w : Fin 10 → ℕ)
    (htotal : ∑ r : Fin 10, w r = 2 * N)
    (hsigma0 : w 0 + w 1 + w 2 = 2 * alpha + beta)
    (hsigma2 : w 7 + w 8 + w 9 = 2 * alpha + beta)
    (hmuJ0 : w 3 + w 7 = alpha + gamma)
    (hmuJ3 : w 2 + w 6 = alpha + gamma)
    (hmuK0 : w 6 + w 9 = alpha + gamma)
    (hmuK3 : w 0 + w 3 = alpha + gamma) :
    let p : Fin 10 → ℝ := fun r ↦ (w r : ℝ) / (2 * N : ℕ)
    let sigma : ℝ := (2 * alpha + beta : ℕ) / (N : ℝ)
    let mu : ℝ := (alpha + gamma : ℕ) / (N : ℝ)
    (∀ r, 0 ≤ p r) ∧
      (∑ r : Fin 10, p r) = 1 ∧
      p 0 + p 1 + p 2 = sigma / 2 ∧
      p 7 + p 8 + p 9 = sigma / 2 ∧
      p 3 + p 7 = mu / 2 ∧
      p 2 + p 6 = mu / 2 ∧
      p 6 + p 9 = mu / 2 ∧
      p 0 + p 3 = mu / 2 := by
  sorry
