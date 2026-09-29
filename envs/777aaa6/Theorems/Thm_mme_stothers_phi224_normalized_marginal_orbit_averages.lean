-- Prove2me | Theorems.Thm_mme_stothers_phi224_normalized_marginal_orbit_averages
-- name    : mme_stothers_phi224_normalized_marginal_orbit_averages
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:50:10.714472+00:00
-- url     : https://prove2.me/theorems/baac099b-2b34-48e5-a983-c0f15f6ffdac
-- title:
--   Normalized phi_224 marginals fix the symmetry-orbit averages
-- statement:
--   Let $N>0$, and let $x=(x_0,\ldots,x_8)$ be a normalized real frequency vector whose projected grade marginals are the Davie--Stothers $\varphi_{224}$ marginal counts divided by $2N$. Then its four symmetry-orbit averages are
--
--   $$
--   \frac{x_0+x_8}{2}=\frac{\alpha}{2N},\qquad
--   \frac{x_1+x_3+x_5+x_7}{4}=\frac{\beta}{2N},
--   $$
--
--   $$
--   \frac{x_2+x_6}{2}=\frac{\gamma}{2N},\qquad
--   x_4=\frac{2\delta}{2N}.
--   $$
--
--   This is the probability-vector form of the orbit-average classification, suitable for direct use in multinomial entropy estimates.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), equations (3.5)--(3.6) and the phi_224 marginals in Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_marginal_orbit_averages

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_normalized_marginal_orbit_averages
    (N alpha beta gamma delta : ℕ) (hN : 0 < N) (x : Fin 9 → ℝ)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      (∑ r : Fin 9,
        if MME.StothersFourth.Phi224.pattern r i = s then x r else 0) =
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s : ℝ) / ((2 * N : ℕ) : ℝ)) :
    (x 0 + x 8) / 2 =
        (alpha : ℝ) / ((2 * N : ℕ) : ℝ) ∧
      (x 1 + x 3 + x 5 + x 7) / 4 =
        (beta : ℝ) / ((2 * N : ℕ) : ℝ) ∧
      (x 2 + x 6) / 2 =
        (gamma : ℝ) / ((2 * N : ℕ) : ℝ) ∧
      x 4 = ((2 * delta : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) := by
  sorry
