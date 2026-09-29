-- Prove2me | Theorems.Thm_mme_stothers_phi233_orbit_entropy_symmetrization
-- name    : mme_stothers_phi233_orbit_entropy_symmetrization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:52:54.733586+00:00
-- url     : https://prove2.me/theorems/45708920-2aa3-4c5a-9782-18859ecead79
-- title:
--   Orbit averaging increases phi_233 profile entropy
-- statement:
--   Let $x_0,\ldots,x_9$ be nonnegative weights on the ten ordered $\varphi_{233}$ joint types. Average the weights over the four symmetry orbits
--
--   $$
--   \{0,2,7,9\},\qquad \{1,8\},\qquad \{3,6\},\qquad \{4,5\}.
--   $$
--
--   Then Shannon's natural-log entropy does not decrease:
--
--   $$
--   \sum_{r=0}^{9} -x_r\log x_r \;\le\; 4h\!\left(\frac{x_0+x_2+x_7+x_9}{4}\right) +2h\!\left(\frac{x_1+x_8}{2}\right) +2h\!\left(\frac{x_3+x_6}{2}\right) +2h\!\left(\frac{x_4+x_5}{2}\right),
--   $$
--
--   where $h(t)=-t\log t$ with $h(0)=0$. This is the concrete symmetrization step that reduces the entropy maximum over all same-marginal completions to the four-parameter symmetric fibre used by Davie--Stothers.
-- source:
--   Concavity of Shannon entropy; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 symmetry reduction preceding Equation (3.6), pp. 359--360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_orbit_entropy_symmetrization
    (x : Fin 10 → ℝ) (hx : ∀ r, 0 ≤ x r) :
    (∑ r : Fin 10, Real.negMulLog (x r)) ≤
      4 * Real.negMulLog ((x 0 + x 2 + x 7 + x 9) / 4) +
      2 * Real.negMulLog ((x 1 + x 8) / 2) +
      2 * Real.negMulLog ((x 3 + x 6) / 2) +
      2 * Real.negMulLog ((x 4 + x 5) / 2) := by
  sorry
