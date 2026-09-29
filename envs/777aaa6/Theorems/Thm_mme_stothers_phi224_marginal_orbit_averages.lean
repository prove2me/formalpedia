-- Prove2me | Theorems.Thm_mme_stothers_phi224_marginal_orbit_averages
-- name    : mme_stothers_phi224_marginal_orbit_averages
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:35:32.671305+00:00
-- url     : https://prove2.me/theorems/b69d68ce-8146-4e1c-bc0c-a62c67e6b249
-- title:
--   Phi_224 marginals fix all four symmetry-orbit averages
-- statement:
--   Let $x_0,\ldots,x_8$ be real weights on the nine fine types of $\varphi_{224}$. If their three projected grade marginals equal the Davie--Stothers marginals with parameters $\alpha,\beta,\gamma,\delta$, then the averages on the four symmetry orbits are fixed:
--
--   $$
--   \frac{x_0+x_8}{2}=\alpha,\qquad
--   \frac{x_1+x_3+x_5+x_7}{4}=\beta,\qquad
--   \frac{x_2+x_6}{2}=\gamma,\qquad
--   x_4=2\delta.
--   $$
--
--   Thus every point of the full same-marginal polytope has the same orbit symmetrization as the distinguished profile. Combined with concavity of entropy, this proves that nonsymmetric completions cannot have a larger exponential rate.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the type-2 symmetry reduction (3.6) and the phi_224 marginals in Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_marginal_orbit_averages
    (alpha beta gamma delta : ℕ) (x : Fin 9 → ℝ)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      (∑ r : Fin 9,
        if MME.StothersFourth.Phi224.pattern r i = s then x r else 0) =
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s : ℝ)) :
    (x 0 + x 8) / 2 = alpha ∧
      (x 1 + x 3 + x 5 + x 7) / 4 = beta ∧
      (x 2 + x 6) / 2 = gamma ∧
      x 4 = 2 * delta := by
  sorry
