-- Prove2me | Theorems.Thm_mme_stothers_phi224_orbit_entropy_symmetrization
-- name    : mme_stothers_phi224_orbit_entropy_symmetrization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:33:01.507731+00:00
-- url     : https://prove2.me/theorems/adaa6c7a-5acf-4eaf-a42e-9b5187cfe5cd
-- title:
--   Entropy increases under phi_224 orbit symmetrization
-- statement:
--   For a nonnegative frequency vector $x=(x_0,\ldots,x_8)$ on the nine fine types of $\varphi_{224}$, averaging within the four symmetry orbits cannot decrease entropy. Explicitly,
--
--   $$
--   \sum_{r=0}^{8}-x_r\log x_r\leq
--   2h\!\left(\frac{x_0+x_8}{2}\right)+
--   4h\!\left(\frac{x_1+x_3+x_5+x_7}{4}\right)+
--   2h\!\left(\frac{x_2+x_6}{2}\right)+h(x_4),
--   $$
--
--   where $h(t)=-t\log t$ with $h(0)=0$. The orbit sizes are $2,4,2,1$. This is the concavity step that reduces the type-2 same-marginal entropy maximum for $\varphi_{224}$ to the symmetric subspace.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the symmetry reduction in the type-2 estimate (3.6) and Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_orbit_entropy_symmetrization
    (x : Fin 9 → ℝ) (hx : ∀ r, 0 ≤ x r) :
    (∑ r : Fin 9, Real.negMulLog (x r)) ≤
      2 * Real.negMulLog ((x 0 + x 8) / 2) +
      4 * Real.negMulLog ((x 1 + x 3 + x 5 + x 7) / 4) +
      2 * Real.negMulLog ((x 2 + x 6) / 2) +
      Real.negMulLog (x 4) := by
  sorry
