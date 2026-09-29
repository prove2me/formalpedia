-- Prove2me | Theorems.Thm_mme_stothers_phi224_normalized_same_marginal_entropy_maximum
-- name    : mme_stothers_phi224_normalized_same_marginal_entropy_maximum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:14:35.771158+00:00
-- url     : https://prove2.me/theorems/204738f5-d423-43f6-82b2-b1ecb1273341
-- title:
--   The normalized exact phi_224 profile maximizes same-marginal entropy
-- statement:
--   Let $N>0$, and let $x=(x_0,\ldots,x_8)$ be any nonnegative normalized frequency vector on the nine fine types of $\varphi_{224}$ whose projected marginals equal the Davie--Stothers marginal counts divided by $2N$. Then
--
--   $$
--   \sum_{r=0}^{8}-x_r\log x_r\leq
--   2h\!\left(\frac{\alpha}{2N}\right)+
--   4h\!\left(\frac{\beta}{2N}\right)+
--   2h\!\left(\frac{\gamma}{2N}\right)+
--   h\!\left(\frac{2\delta}{2N}\right),
--   $$
--
--   where $h(t)=-t\log t$ with $h(0)=0$. The right side is exactly the entropy of the normalized distinguished profile, so this bounds every nonsymmetric completion at the source exponential rate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), equations (3.5)--(3.6) and Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_normalized_marginal_orbit_averages
import Theorems.Thm_mme_stothers_phi224_orbit_entropy_symmetrization

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_normalized_same_marginal_entropy_maximum
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (x : Fin 9 → ℝ) (hx : ∀ r, 0 ≤ x r)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      (∑ r : Fin 9,
        if MME.StothersFourth.Phi224.pattern r i = s then x r else 0) =
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s : ℝ) / ((2 * N : ℕ) : ℝ)) :
    (∑ r : Fin 9, Real.negMulLog (x r)) ≤
      2 * Real.negMulLog
        ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
      4 * Real.negMulLog
        ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
      2 * Real.negMulLog
        ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
      Real.negMulLog
        (((2 * delta : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)) := by
  sorry
